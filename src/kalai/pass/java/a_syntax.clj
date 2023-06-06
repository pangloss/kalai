(ns kalai.pass.java.a-syntax
  (:require [kalai.util :as u]
            [pattern :refer [directed rule-list rule sub subm descend descend-all success]]))

;;; -------- language constructs to syntax
;; expanded s-expressions below


;; what is an expression?
;; can occur in a statement, block, conditional etc...

;; what is a statement?
;; what expressions cannot be statements? block, x/if
;; expression semicolon
;;  3;
;;  x++;
;; if (x==1) x++;
;; if (x==1) {
;;    x++;
;; }
;; expression statements, declaration statements, and control flow statements


;; f(x+1, 3);
;; f(g(x+1), 3);

;; what is a block?
;; public static void f() { }
;; { {} }

;; what is an assignment?
;; what is a conditional?
;; what is a function definition?
;; what is an invocation

;; what expressions can be arguments to functions?
;; invocations, assignments maybe, literals, variables, ternaries maybe

;; expressions can contain other expressions
;; expressions cannot contain statements
;; statements can contain other statements
;; statements can contain expressions
;; block must contain statements (not expressions)

;;
;; Rules
;;


(defn get-t [x]
  (:t (meta x)))

(declare statement)

(def expression
  (directed
    (rule-list
      (rule create-empty-collection
        '(& (| [] {} #{}) ?this)
        (sub (j/new ~(:t (meta this)))))

      ;; mutable vector ^{:t {:mvector [_]}} []
      (rule mutable-vector
        '(& (?:chain (? expr vector?) get-t (? t #{:mvector}))
           [??->x*])
        (let [tmp (u/tmp t expr)
              exprs (for [x x*]
                      (sub (j/expression-statement (j/method add ?tmp ?x))))]
          (sub (group (j/init ?tmp (j/new ?t)) ??exprs ?tmp))))

      ;; persistent vector ^{:t {:vector [_]}} []
      ;; or any other type on a vector literal
      (rule persistent-vector
        '(& (? expr vector?) [??->x*])
        (let [t (get-t expr)
              t (if (= t :any) {:vector [:any]} t)]
          (u/preserve-type expr
            (reduce (fn [form x] (sub (j/method addLast ?form ?x)))
              (sub (j/new ?t))
              x*))))

      ;; mutable map ^{:t {:mmap [_]}} {}
      (rule mutable-map
        '(?:chain (? expr map?) get-t (? t #{:mmap}))
        (let [kvs (map (fn [[k v]] [(descend k) (descend v)]) (u/sort-any-type expr))
              tmp (u/tmp t expr)
              exprs (map (fn [[k v]] (sub (j/expression-statement (j/method put ?tmp ?k ?v)))) kvs)]
          (sub (group (j/init ?tmp (j/new ?t)) ??exprs ?tmp))))


      ;; persistent map ^{:t {:map [_]}} {}
      ;; or any other type on a map literal
      (rule persistent-map
        '(? expr map?)
        (let [t (get-t expr)
              t (if (= t :any) {:map [:any :any]} t)]
          (u/preserve-type expr
            (reduce (fn [form [k v]]
                      (let [k (descend k)
                            v (descend v)]
                        (sub (j/method put ?form ?k ?v
                               io.lacuna.bifurcan.Maps.MERGE_LAST_WRITE_WINS))))
              (sub (j/new ?t))
              (u/sort-any-type expr)))))

      (rule mutable-set
        '(?:chain (? expr set?) get-t (? t #{:mset}))
        (let [x* (descend-all (u/sort-any-type expr))
              tmp (u/tmp t expr)
              exprs (for [x x*]
                      (sub (j/expression-statement (j/method add ?tmp ?x))))]
          (sub (group (j/init ?tmp (j/new ?t)) ??exprs ?tmp))))

      (rule persistent-set
        '(? expr set?)
        (let [x* (descend-all (u/sort-any-type expr))
              t (get-t expr)
              t (if (= t :any) {:set [:any]} t)]
          (u/preserve-type expr
            (reduce (fn [form x] (sub (j/method add ?form ?x)))
              (sub (j/new ?t))
              x*))))

      (rule interop
        '(new ?c ??->args)
        (sub (j/new ?c ??args)))

      (rule operator-usage
        '(operator ?op ??->args)
        (sub (j/operator ?op ??args)))

      (rule function-invocation
        '(invoke ?f ??->args)
        (subm (j/invoke ?f ??args)))

      (rule method-invocation
        '(method ?method ?->object ??->args)
        (sub (j/method ?method ?object ??args)))

      (rule lambda-function
        '(lambda ?name ?docstring ?body)
        (sub (j/lambda ?name ?docstring ?body)))

      (rule if1
        '(if ?->condition ?then)
        (let [tmp (u/tmp-for then)]
          (sub (group
                 (j/init ~(u/maybe-meta-assoc tmp :mut true))
                 (j/if ?condition
                   (j/block (j/assign ?tmp ~(descend then))))
                 ?tmp))))

      (rule if2
        '(if ?->condition ?then ?->else)
        (let [tmp (u/tmp-for then)]
          (sub (group
                 (j/init ~(u/maybe-meta-assoc tmp :mut true))
                 (j/if ?condition
                   (j/block (j/assign ?tmp ~(descend then)))
                   (j/block (j/assign ?tmp ?else)))
                 ?tmp))))

      (rule do-block
        '(do ??x ?->last)
        (let [x (map statement x)]
          (sub (group ??x ?last))))

      (rule case
        '(case ?->x (?:* ?k ?->v))
        (sub (j/switch ?x
               (j/block (?:* ?k (j/expression-statement ?v)))))))))

(def init
  (rule-list
    (rule '(init ?name)
      (sub (j/init ?name)))

    (rule '(init ?name ?x)
      (sub (j/init ?name ~(expression x))))))

(def top-level-init
  (rule-list
    (rule '(init ?name)
      (sub (j/init ~(u/maybe-meta-assoc name :global true))))

    (rule '(init ?name ?x)
      (sub (j/init ~(u/maybe-meta-assoc name :global true) ~(expression x))))))

(def statement
  (directed
    {:fn-map {'>> expression}}
    (rule-list
      init

      (rule return
        '(return ?>>x)
        (sub (j/expression-statement (j/return ?x))))

      (rule 'while
        '(while ?>>condition ??->body)
        (sub
          (j/while ?condition
            (j/block ??body))))

      (rule 'foreach
        '(foreach ?sym ?>>xs ??->body)
        (sub (j/foreach ?sym ?xs
               (j/block ??body))))

      (rule conditional1
        '(if ?>>test ?->then)
        (sub (j/if ?test
               (j/block ?then))))

      (rule conditional2
        '(if ?>>test ?->then ?->else)
        (sub (j/if ?test
               (j/block ?then)
               (j/block ?else))))

      (rule case
        '(case ?>>x (?:* ?k ?>>v) ?default)
        (sub (j/switch ?x
               (j/block (?:* (j/case ?k (j/expression-statement ?v)))
                 (j/default ?default)))))

      (rule do
        '(do ??->xs)
        (sub (j/block ??xs)))

      (rule assign
        '(assign ?name ?>>value)
        (sub (j/assign ?name ?value)))

      (rule other-expr
        '(& (|
              (assign ??_)
              (operator ++ ?_)
              (operator -- ?_)
              (method ??_)
              (invoke ??_)
              (new ??_))
           ?>>expr)
        (sub (j/expression-statement ?expr)))

      ;; Java does not allow other expressions as statements
      (rule otherwise
        '?else
        (success nil)))))


(def function
  (rule function
    '(function ?name ?params ??body)
    (let [body (map statement body)]
      (sub (j/function ?name ?params (j/block ??body))))))

(def top-level-form
  (rule-list
    function
    top-level-init
    (rule otherwise
      '?else
      (throw (ex-info "Expected a top level form" {:else else})))))

(def rewrite
  (rule-list
    (rule
      '(namespace ?ns-name ??forms)
      (let [forms (map top-level-form forms)]
        (sub (j/class ?ns-name
               (j/block ??forms)))))

    (rule otherwise
      '?else
      (throw (ex-info "Expected a namespace" {:else else})))))
