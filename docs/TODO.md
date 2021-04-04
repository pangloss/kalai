# TODO

* Create a task in `examples` to run the logic tests
* Verify that examples can compile using deployed artifact (namely, if/how to update deps.clj and/or pom.xml)
* Rust etc
    - dealing with refs?
    - do we make the user annotate the type in every assignment?
    - or do we infer this in the S-exprs?
    - how do we know when to deref a ref vs. not deref when it is not a ref (ex: Vec.insert() in demo_02.rs code)
    - or what should the question be?
    - current workaround in demo02.clj
      - annotated the types manually in the code
      - ex: `^:ref ^{:t {:mvector [:char]}} numberSystemDigits (get numberSystemsMap numberSystem)`
        (which used to be `^{:t {:mvector [:char]}} numberSystemDigits (get numberSystemsMap numberSystem)`)
  - parameterize pipeline & test helpers to be target lang-driven
  - add Java tests to Rust tests that we skipped over for temporary expediency reasons
  - things that were difficult for emitter approach in Rust
    - type modifiers
      - if a fn param is both mutable and a reference
        - fn param signature (ex1: `s: &String;` ex2: `s: &mut String`)
        - annotation of call site arg expression to the fn param (ex1: `f(&my_string)`, ex2: `f(&mut my_string)`)
        - but if `my_string` was previously defined as `let my_string: &String = &String::from("...")`, then call site would look different (ex1: `f(my_string)`, ex2: `f(mut my_string)`) to prevent passing a `&&String` type
    - general type strategy that Kalai enforces
      - primitive types to be "pass-by-value"
      - all other types to be "pass-by-reference" (all other types = heap-allocated?)
    - interop
  - make shared passes apply for all target languages
    - if so, can make them ignore leading target language symbol prefix (ex: "j/", "r/")
    - a block is just a block, why bother with r/block, j/block
  - StringBuffer mutability should be inferred
  
* Types!!!
  - Document target language type conversions (when added)
  - Validate types and narrow the set of accepted types
  - Define common types
    - supporting universals: numeric types should be signed
  - Top level def of data literal needs static block initialization `(def x [1])` for Java
  - Debug why `^Character localDigit (get numberSystemDigits remainder)` transpiles to a type declaration of `Object` but `^{:t :char} localDigit (get numberSystemDigits remainder)` gives the proper type `char` in demo02. Same for `^char sep`.
  - Troubleshoot issue in `getNumberSystemsMap` in demo02 where data literal to be return must have type annotation within a `let` binding else types are missing in Kalai compilation phase (note: also the only nested data structure in demo02)
  - Might be a nice-to-have to propagate function return type to variable identifier in variable assignments, ex: `(def x (fn-call 1 2 3))`
  - Propagate return type of fn to a data literal passed as return value in fn body implementation, ex: `(defn f ^{:t {:mmap [:char :int]}} [] {})`
  - Option types
  - (let [x (String. "abc")]) should infer :t :string
    * does this already happen 
    * also, consider turning "user-defined types" (non-Kalai supported primitives) (ex: `'java.lang.StringBuffer`) into Kalai style
    target-language type representation in target-language pipeline phase (ex: Rust syntax pass converts `'StringBuffer` into
      `{:mvector [:char]}` as early as possible)
* Test organization
  - grouping functionality
  - generate docsy from tests
    - new test directory
    - split up into more namespaces
    - don't show the Kalai intermediate syntax
    - markdown inversion
    - GitHub action
    - local action
  - Resurect placation or find some way of doing that better
* Interop
  - Add demo03 from https://github.com/echeran/kalai/pull/13 (environment variables)
  - Support import statements (ex: for user-defined classes; automatically created when user uses data collections)
  - expand the "function-call" pass (core/interop/kalai/custom)
    - depends on us choosing another target language
    - core = clojure.core fns; interop = which Java classes to support (ex: StringBuffer) out-of-the-box; kalai = other users' Kalai source; custom = 3rd-party libs/fns that users need
  - see if starter code for rust and python works
  - support array types (?) (ex: Java main method)
  - In C++ make sure that string concatenation of numbers is wrapped by std::to_string https://stackoverflow.com/questions/191757/how-to-concatenate-a-stdstring-and-an-int
  - implement `str`
* Extend demo01 and demo02
  - try using `case` instead of `cond` in `getSeparatorPositions` of demo02
  - transpile logic unit tests into target languages
* Miscellaneous
  - Filename syntax should be language specific
  - Update Design doc headings & organization
  - Throw warning/error if expression cannot be supported as statement in target language (target-language's a_syntax.clj)
  - Delete the line "import java.util.List" from Java pipeline's e-string/std-imports
* We think we have most of the proof of concept language concepts, but we need to hook up the tests
  - workflows (developer and CI)
    * documenting workflows (?)
  - salvaging existing tests
  - figure out coverage testing
  - figure out feature coverage across languages / feature parity
  - indenting strings and comparing ignoring leading space
  - elseif
  - run the output through the native language compiler
  - pleasant cider testing
* Persistent data structures
  - depends on import statements being intelligent (not hard-coded)
  - all languages have a library, but not everyone wants the dependency
  - performance goals
  - would like to support both, choose the mutability that you want
  - need to differentiate (probably by atoms)
  - consider our own macros
  - maps/sets/vectors conj/assoc/update etc
  - import when needed
  - We might be better of using Collection builder functions instead of temporary variables?
  - We should check static block semantics
* Operator and language specific transformation (e.g. = in Clojure is either .equals java or ==)
* test helper clean up
  - don't report failures twice
* Support function calls where functions are defined in input code across namespaces
  - Solve importing
* Allow users to bring their own functions
* Allow users to bring their own languages
* Indentation
* Do we support first class enums?
  - Without it you lose type strictness
  - Namespaced keywords?
  - Would require user declaration form
* Expand documentation:
  - Preserving knowledge (not tribal)
  - Keeping on track (what did we learn, why did we do that)