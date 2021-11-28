#lang racket
(require (lib "eopl.ss" "eopl"))
(require parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         parser-tools/yacc)

;necessary datatypes for grammer:

(define-datatype program progarm?
  (a-program
   (stmts statements?)))

(define-datatype statements statements?
  (a-statement
   (stmt statement?))
  (multi-statements
   (stmt statement?)
   (stmts statements?)))

(define (identifier? x) (and (not (or
                                   (equal? x 'def)
                                   (equal? x 'pass)
                                   (equal? x 'break)
                                   (equal? x 'continue)
                                   (equal? x 'global)
                                   (equal? x 'if)
                                   (equal? x 'else)
                                   (equal? x 'for)
                                   (equal? x 'in)
                                   (equal? x 'or)
                                   (equal? x 'and)
                                   (equal? x 'not)
                                   (equal? x 'True)
                                   (equal? x 'False)
                                   (equal? x 'None)))
                             (symbol? x)))

;merging simple and compound statement into statement 
(define-datatype statement statement?
  (pass-stmt)
  (break-stmt)
  (continue-stmt)
  (assign-stmt
   (id identifier?)
   (exp expression?))
  (return-stmt-no-exp)
  (return-stmt
   (exp expression?))
  (global-stmt
   (id identifier?))
  (funcdef-stmt      ;merged parameter-less and with parameter functions
   (id identifier?)
   (prms params?)
   (stmts statements?))
  (if-stmt
   (exp expression?)
   (true-stmts statements?)
   (false-stmts statements?))
  (for-stmt
   (id identifier?)
   (exp expression?)
   (stmts statements?))
  (print-stmt
   (exp expression?)))

(define-datatype params params?
  (no-param)
  (multi-params
   (id identifier?)
   (exp expression?)
   (prms params?)))

(define-datatype expression expression?
  (a-expression
   (disj disjunction?)))

(define-datatype disjunction disjunction?
  (a-disjunction
   (conj conjunction?))
  (or-disjunction
   (disj disjunction?)
   (conj conjunction?)))

(define-datatype conjunction conjunction?
  (a-conjunction
   (inv inversion?))
  (and-conjunction
   (conj conjunction?)
   (inv inversion?)))

(define-datatype inversion inversion?
  (not-inversion
   (inv inversion?))
  (comparison-inversion
   (cmpr comparison?)))

(define-datatype comparison comparison?
  (sum-comparison
   (a-sum sum?))
  (compare-op-comparison
   (a-sum sum?)
   (cmpr-sum-pairs compare-op-sum-pairs?)))

(define-datatype compare-op-sum-pairs compare-op-sum-pairs?
  (a-compare-op-sum-pair
   (a-cmpr-sum-pair compare-op-sum-pair?))
  (multi-compare-op-sum-pairs
   (a-cmpr-sum-pair compare-op-sum-pair?)
   (cmpr-sum-pairs compare-op-sum-pairs?)))

(define-datatype compare-op-sum-pair compare-op-sum-pair?
  (eq-sum
   (a-sum sum?))
  (lt-sum
   (a-sum sum?))
  (gt-sum
   (a-sum sum?)))

(define-datatype sum sum?
  (term-sum
   (a-term term?))
  (add-sum
   (a-sum sum?)
   (a-term term?))
  (sub-sum
   (a-sum sum?)
   (a-term term?)))

(define-datatype term term?
  (factor-term
   (a-factor factor?))
  (mult-term
   (a-term term?)
   (a-factor factor?))
  (div-term
   (a-term term?)
   (a-factor factor?)))

(define-datatype factor factor?
  (power-factor
   (a-power power?))
  (pos-factor
   (a-factor factor?))
  (neg-factor
   (a-factor factor?)))

(define-datatype power power?
  (primary-power
   (a-primary primary?))
  (pow-power
   (a-atom atom?)
   (a-factor factor?)))

(define-datatype primary primary?
  (atom-primary
   (a-atom atom?))
  (call-primary
   (a-primary primary?)
   (args arguments?))
  (getlist-primary
   (a-primary primary?)
   (exp expression?)))

(define-datatype arguments arguments?
  (no-argument)
  (multi-arguments
   (exp expression?)
   (args arguments?)))

(define-datatype atom atom?
  (id
   (id identifier?))
  (number
   (num number?))
  (true)
  (false)
  (none)
  (a-explist   
   (lst explist?)))

;merged explist and expressions
(define-datatype explist explist?   ;named it explist so that it won't get confused with racket list function
  (empty-list)
  (cons-list
   (exp expression?)
   (lst explist?)))

;********************************************
;store, environment and expval datatype:

;store:
(define empty-store
  (lambda () '()))

(define the-store (empty-store))

(define get-store
  (lambda () the-store))

(define reference?
  (lambda (v)
    (integer? v)))

(define newref
  (lambda (val)
    (let ((next-ref (length the-store)))
      (set! the-store (append the-store (list val)))
      next-ref)))

(define deref
  (lambda (ref)
    (list-ref the-store ref)))

(define setref!
  (lambda (ref val)
    (set! the-store
          (letrec
              ((setref-inner
                (lambda (store1 ref1)
                  (cond
                    ((null? store1)
                     (raise "error"))
                    ((zero? ref1)
                     (cons val (cdr store1)))
                    (else
                     (cons
                      (car store1)
                      (setref-inner
                       (cdr store1) (- ref1 1))))))))
            (setref-inner the-store ref)))))

;expval
(define-datatype expval expval?
  (num-val (num number?))
  (bool-val (bool boolean?))
  (list-val (lst (list-of expval?)))
  (func-val (f func?))
  (none-val))

(define expval->num
  (lambda (val)
    (cases expval val
      (num-val (num) num)
      (else (raise "not a num-val")))))

(define expval->bool
  (lambda (val)
    (cases expval val
      (bool-val (bool) bool)
      (else (raise "not a bool-val")))))

(define expval->list
  (lambda (val)
    (cases expval val
      (list-val (lst) lst)
      (else (raise "not a list-val")))))

(define expval->func
  (lambda (val)
    (cases expval val
      (func-val (f) f)
      (else (raise "not a func-val")))))

(define expval->val
  (lambda (val)
    (cases expval val
          (func-val (f) "function")
          (num-val (n) n)
          (bool-val (b) b)
          (list-val (lst) (letrec ((list-val->list-of-val
                                    (lambda (lst)
                                      (if (null? lst)
                                          '()
                                          (cons
                                           (expval->val (car lst))
                                           (list-val->list-of-val (cdr lst)))))))
                            (list-val->list-of-val lst)))
          (none-val () "None"))))

;env:
(define-datatype environment environment?
  (empty-env)
  (extend-env
   (var identifier?)
   (val reference?)
   (environment environment?))
  (extend-env-def
   (func-name identifier?)
   (func-prms params?)
   (func-stmts statements?)
   (eval-env environment?)
   (saved-env environment?)))

;global-env: whenever we have a function call, this gets updated
(define global-env (empty-env))

(define (set-global-env! new-env)
  (set! global-env new-env))

(define has-set-global-env #f)

(define-datatype func func?
  (function
   (func-prms params?)
   (func-stmts statements?)
   (evaluation-env environment?)
   ))

(define (apply-env env var)
  (cases environment env
    (empty-env () 'not-initialized)
    (extend-env (saved-var saved-val saved-env) (if (equal? var saved-var)
                                                    saved-val
                                                    (apply-env saved-env var)))
    (extend-env-def (func-name func-prms func-stmts eval-env saved-env)
                    (if (equal? var func-name)
                        (newref (func-val (function func-prms func-stmts eval-env)))
                        (apply-env saved-env var)))))

(define (value-of-program pgm)
  (cases program pgm
    (a-program (stmts)
               (begin
                 (value-of-statements stmts (empty-env))
                 (void)))))

;result datatype for value of statement(s):
(define-datatype result result?
  (return-res
   (val expval?))
  (void-res
   (env environment?))
  (continue-res)
  (break-res))

(define (value-of-statements stmts env)
  (cases statements stmts
    (a-statement (stmt)
                 (value-of-statement stmt env))
    (multi-statements (stmt saved-stmts)
                      (let ((res (value-of-statement stmt env)))
                        (cases result res
                          (void-res (new-env) (value-of-statements saved-stmts new-env))
                          (else res))))))

(define (value-of-statement stmt env)
  (cases statement stmt
    (pass-stmt () (void-res env))
    (break-stmt () (break-res))
    (continue-stmt () (continue-res))
    (assign-stmt (id exp)
                (let ((ref (apply-env env id)))
                    (if (equal? ref 'not-initialized)
                        (void-res (extend-env id (newref (a-thunk exp env)) env))
                        (begin
                          (setref! ref (value-of-expression exp env))
                          (void-res env)))))
    (return-stmt-no-exp () (return-res (none)))
    (return-stmt (exp)
                 (let ((val (value-of-expression exp env)))
                   (return-res val)))
    (global-stmt (id)
                (void-res (extend-env id (apply-env global-env id) env)))
    (funcdef-stmt (id parameters stmts)
                  (void-res (extend-env-def id parameters stmts env env)))
    (if-stmt (exp true-statements false-statements)
             (let ((bool (expval->bool (value-of-expression exp env))))
               (let ((res (value-of-statements
                           (if bool true-statements false-statements)
                           env)))
                 (cases result res
                   (void-res (res-env) (void-res env)) ;new variables in if-stmt can not be accessed outside of if
                   (else res))))) 
    (for-stmt (id exp stmts)
              (let ((for-list (expval->list (value-of-expression exp env))))
                (let ((res (value-of-for id for-list stmts env)))
                  (cases result res
                    (return-res (val) res)
                    (else (void-res env)))))) ;same as if
    (print-stmt (exp)
                (begin
                  (println (expval->val (value-of-expression exp env)))
                  (void-res env)))
    ))

(define (value-of-for var list stmts env)
  (if (null? list)
      (void-res env)
      (let ((res1 (value-of-statements stmts (extend-env var (newref (car list)) env))))
        (cases result res1
          (return-res (val) res1)
          (break-res () (void-res env))
          (else (value-of-for var (cdr list) stmts env))))))

;************************
;value-of expression
(define (evaluate addr)
    (run (port->string (open-input-file addr) #:close? #t)))

(define (value-of-expression exp env)
  (cases expression exp
    (a-expression (disj) (value-of-disjunction disj env))))

(define (value-of-disjunction disj env)
  (cases disjunction disj
    (a-disjunction (conj) (value-of-conjunction conj env))
    (or-disjunction (disj conj)
                     (let ((b1 (expval->bool (value-of-disjunction disj env)))
                           (b2 (expval->bool (value-of-conjunction conj env))))
                       (bool-val (or b1 b2))))))

(define (value-of-conjunction conj env)
  (cases conjunction conj
    (a-conjunction (inv) (value-of-inversion inv env))
    (and-conjunction (conj inv)
                     (let ((b1 (expval->bool (value-of-conjunction conj env))))
                       (bool-val (if b1
                                     (expval->bool (value-of-inversion inv env))
                                     #f))))))

(define (value-of-inversion inv env)
  (cases inversion inv
    (not-inversion (inv)
                   (let ((b (expval->bool (value-of-inversion inv env))))
                     (bool-val (not b))))
    (comparison-inversion (cmpr) (value-of-comparison cmpr env))))

(define (value-of-comparison cmpr env)
  (cases comparison cmpr
    (sum-comparison (a-sum) (value-of-sum a-sum env))
    (compare-op-comparison (a-sum cmpr-sum-pairs) (value-of-compare-op-sum-pairs a-sum cmpr-sum-pairs env))))

(define (value-of-compare-op-sum-pairs s cosps env)
  (cases compare-op-sum-pairs cosps
    (a-compare-op-sum-pair (cosp)
                           (cases compare-op-sum-pair cosp
                             (eq-sum (a-sum) (bool-val (equal? (value-of-sum s env) (value-of-sum a-sum env))))
                             (lt-sum (a-sum)
                                      (let ((a (expval->num (value-of-sum s env)))
                                            (b (expval->num (value-of-sum a-sum env))))
                                        (bool-val (< a b))))
                             (gt-sum (a-sum)
                                      (let ((a (expval->num (value-of-sum s env)))
                                            (b (expval->num (value-of-sum a-sum env))))
                                        (bool-val (> a b))))))
    (multi-compare-op-sum-pairs (cosp cosps)
                               (cases compare-op-sum-pair cosp
                                 (eq-sum (a-sum)
                                         (if (equal? (value-of-sum s env) (value-of-sum a-sum env))
                                             (value-of-compare-op-sum-pairs a-sum cosps env)
                                             (bool-val #f)))
                                 (lt-sum (a-sum)
                                      (let ((a (expval->num (value-of-sum s env)))
                                            (b (expval->num (value-of-sum a-sum env))))
                                        (if (< a b)
                                            (value-of-compare-op-sum-pairs a-sum cosps env)
                                            (bool-val #f))))
                                 (gt-sum (a-sum)
                                         (let ((a (expval->num (value-of-sum s env)))
                                               (b (expval->num (value-of-sum a-sum env))))
                                           (if (> a b)
                                               (value-of-compare-op-sum-pairs a-sum cosps env)
                                               (bool-val #f))))))))

(define (value-of-sum a-sum env)
  (cases sum a-sum
    (term-sum (tr) (value-of-term tr env))
    (add-sum (a-sum tr)
             (let ((a (value-of-sum a-sum env))
                   (b (value-of-term tr env)))
               (cases expval a
                 (num-val (x) (num-val (+ x (expval->num b))))
                 (bool-val (x) (bool-val (or x (expval->bool b))))
                 (list-val (x) (list-val (append x (expval->list b))))
                 (esle (raise "cannot use + on these operands")))))
    (sub-sum (a-sum tr)
             (let ((a (expval->num (value-of-sum a-sum env)))
                   (b (expval->num (value-of-term tr env))))
               (num-val (- a b))))))

(define (value-of-term tr env)
  (cases term tr
    (factor-term (fac) (value-of-factor fac env))
    (mult-term (tr fac)
               (let ((a (value-of-term tr env))
                     (b (value-of-factor fac env)))
                 (cases expval a
                   (num-val (x) (if (zero? x)
                                    (num-val 0)
                                    (num-val (* x (expval->num b)))))
                   (bool-val (x) (if x
                                     (bool-val (expval->bool b))
                                     (bool-val #f)))
                   (else (raise "cannot use * on these operands")))))
    (div-term (tr fac)
               (let ((a (expval->num (value-of-term tr env)))
                     (b (expval->num (value-of-factor fac env))))
                 (num-val (/ (exact->inexact a) (exact->inexact b)))))))

(define (value-of-factor fac env)
  (cases factor fac
    (power-factor (pow) (value-of-power pow env))
    (pos-factor (fac)
                (let ((a (expval->num (value-of-factor fac env))))
                  (num-val a)))
    (neg-factor (fac)
                (let ((a (expval->num (value-of-factor fac env))))
                  (num-val (- a))))))

(define (value-of-power pow env)
  (cases power pow
    (primary-power (pr) (value-of-primary pr env))
    (pow-power (atm fac)
               (let ((a (expval->num (value-of-atom atm env)))
                     (b (expval->num (value-of-factor fac env))))
                  (num-val (expt a b))))))

(define (value-of-primary pr env)
  (cases primary pr
    (atom-primary (a-atom) (value-of-atom a-atom env))
    (call-primary (a-primary args)
                  (let ((func (expval->func (value-of-primary a-primary env))))
                    (apply-function func args env)))
    (getlist-primary (a-primary exp)
                     (let ((lst (expval->list (value-of-primary a-primary env)))
                           (index (expval->num (value-of-expression exp env))))
                       (if (and (integer? index) (>= index 0) (< index (length lst)))
                           (list-ref lst index)
                           (raise "index not valid"))))))

(define (value-of-atom atm env)
  (cases atom atm
    (id (var) (let ((ref1 (apply-env env var)))
                (let ((w (deref ref1)))
                  (if (expval? w)
                      w
                      (let ((val1 (value-of-thunk w)))
                        (begin
                          (setref! ref1 val1)
                          val1))))))
    (number (num) (num-val num))
    (true () (bool-val #t))
    (false () (bool-val #f))
    (none () (none-val))
    (a-explist (loexp) (list-val (list-value-of-explist loexp env)))))

;returns a list. not a list-val.
(define (list-value-of-explist loexp env)
  (cases explist loexp
    (empty-list () '())
    (cons-list (exp a-explist)
               (cons (value-of-expression exp env) (list-value-of-explist a-explist env)))))

(define (apply-function f args env)
  (cases func f
    (function (prms stmts eval-env)
              ;func-env should contain functions this func know and it's parameters
              (let ((func-env (evaluate-params prms args eval-env env (extract-functions env))))
                (if has-set-global-env
                    (let ((res (value-of-statements stmts func-env)))
                      (cases result res
                        (return-res (val) val)
                        (else (none-val))))
                    (begin
                      (set! has-set-global-env #t)
                      (set-global-env! env)
                      (let ((res (value-of-statements stmts func-env)))
                        (set! has-set-global-env #f)
                        (cases result res
                          (return-res (val) val)
                          (else (none-val))))))))))

(define (extract-functions env)
  (cases environment env
    (empty-env () env)
    (extend-env (var val saved-env)
                (extract-functions saved-env))
    (extend-env-def (func-name func-prms func-stmts eval-env saved-env)
                    (extend-env-def func-name func-prms func-stmts eval-env
                                    (extract-functions saved-env)))))

(define (evaluate-params prms args param-env arg-env retutn-env)
  (cases params prms
    (no-param () retutn-env)
    (multi-params (id param-exp saved-params)
                 (cases arguments args
                   (no-argument ()
                                (evaluate-params saved-params args param-env arg-env
                                                 (extend-env id
                                                             (newref (a-thunk param-exp param-env))
                                                             retutn-env)))
                   (multi-arguments (arg-exp saved-args)
                                   (evaluate-params saved-params saved-args param-env arg-env
                                                    (extend-env id
                                                             (newref (a-thunk arg-exp arg-env))
                                                             retutn-env)))))))

(define-datatype thunk thunk?
  (a-thunk
   (exp1 expression?)
   (env environment?)))

(define value-of-thunk
  (lambda (th)
    (cases thunk th
      (a-thunk (exp1 saved-env)
               (value-of-expression exp1 saved-env)))))

;scan and parse
(define-tokens my-tokens (NUM ID))
(define-empty-tokens my-empty-tokens (EOF NONE \; \: \,
                                          + - * / ** = == < >
                                          and or not
                                          for in pass break continue if else print
                                          def return global
                                          TRUE FALSE
                                          \( \) \[ \]))

(define-lex-abbrevs
  [digit (char-range "0" "9")]
  [num-lex (:: (:+ digit)
              (:? (:: "."
                      (:? (:+ digit)))))]
  [id-lex (:: alphabetic
          (:* (:or alphabetic numeric)))])

(define my-lexer
  (lexer
   [num-lex (token-NUM (string->number lexeme))]
   ["True" (token-TRUE)]
   ["False" (token-FALSE)]
   ["+" (token-+)]
   ["-" (token--)]
   ["*" (token-*)]
   ["/" (token-/)]
   ["**" (token-**)]
   ["=" (token-=)]
   ["==" (token-==)]
   ["<" (token-<)]
   [">" (token->)]
   ["," (token-\,)]
   [":" (token-\:)]
   [";" (token-\;)]
   ["(" (token-\()]
   [")" (token-\))]
   ["[" (token-\[)]
   ["]" (token-\])]
   ["and" (token-and)]
   ["or" (token-or)]
   ["not" (token-not)]
   ["None" (token-NONE)]
   ["def" (token-def)]
   ["return" (token-return)]
   ["global" (token-global)]
   ["for" (token-for)]
   ["in" (token-in)]
   ["pass" (token-pass)]
   ["break" (token-break)]
   ["continue" (token-continue)]
   ["if" (token-if)]
   ["else" (token-else)]
   ["print" (token-print)]
   [whitespace (my-lexer input-port)]
   [(eof) (token-EOF)]
   [id-lex (token-ID (string->symbol lexeme))]))

(define my-parser
  (parser
   (start stmts)
   (end EOF)
   (error void)
   (tokens my-tokens my-empty-tokens)
   (grammar
    [program ((stmts) (a-program $1))]
    [stmts ((stmt \;) (a-statement $1))
           ((stmt \; stmts) (multi-statements $1 $3))]
    [stmt ((pass) (pass-stmt))
          ((break) (break-stmt))
          ((continue) (continue-stmt))
          ((ID = exp) (assign-stmt $1 $3))
          ((global ID) (global-stmt $2))
          ((return exp) (return-stmt $2))
          ((return) (return-stmt-no-exp))
          ((def ID \( prms \) \: stmts) (funcdef-stmt $2 $4 $7))
          ((def ID \( \) \: stmts) (funcdef-stmt $2 (no-param) $6))
          ((if exp \: stmts else \: stmts) (if-stmt $2 $4 $7))
          ((for ID in exp \: stmts) (for-stmt $2 $4 $6))
          ((print exp) (print-stmt $2))]
    [prms ((ID = exp \, prms) (multi-params $1 $3 $5))
          ((ID = exp) (multi-params $1 $3 (no-param)))]
    [exps ((exp) (cons-list $1 (empty-list)))
          ((exp \, exps) (cons-list $1 $3))]
    [exp ((disj) (a-expression $1))]
    [disj ((conj) (a-disjunction $1))
          ((disj or conj) (or-disjunction $1 $3))]
    [conj ((inv) (a-conjunction $1))
          ((conj and inv) (and-conjunction $1 $3))]
    [inv ((not inv) (not-inversion $2))
         ((cmpr) (comparison-inversion $1))]
    [cmpr ((sum cmpr-sum-pairs) (compare-op-comparison $1 $2))
          ((sum) (sum-comparison $1))]
    [cmpr-sum-pairs ((cmpr-sum-pair cmpr-sum-pairs) (multi-compare-op-sum-pairs $1 $2))
                    ((cmpr-sum-pair) (a-compare-op-sum-pair $1))]
    [cmpr-sum-pair ((== sum) (eq-sum $2))
                   ((< sum) (lt-sum $2))
                   ((> sum) (gt-sum $2))]
    [sum ((sum + term) (add-sum $1 $3))
         ((sum - term) (sub-sum $1 $3))
         ((term) (term-sum $1))]
    [term ((term * factor) (mult-term $1 $3))
          ((term / factor) (div-term $1 $3))
          ((factor) (factor-term $1))]
    [factor ((+ factor) (pos-factor $2))
            ((- factor) (neg-factor $2))
            ((power) (power-factor $1))]
    [power ((atom ** factor) (pow-power $1 $3))
           ((primary) (primary-power $1))]
    [primary ((atom) (atom-primary $1))
             ((primary \[ exp \]) (getlist-primary $1 $3))
             ((primary \( \)) (call-primary $1 (no-argument)))
             ((primary \( args \)) (call-primary $1 $3))]
    [args ((exp) (multi-arguments $1 (no-argument)))
          ((exp \, args) (multi-arguments $1 $3))]
    [atom ((ID) (id $1))
          ((NUM) (number $1))
          ((TRUE) (true))
          ((FALSE) (false))
          ((NONE) (none))
          ((explist) (a-explist $1))]
    [explist ((\[ \]) (empty-list))
             ((\[ exps \]) $2)])))

(define (lex-this lexer input) (lambda () (lexer input)))

(define scan&parse
  (lambda (str)
    (let ((input (open-input-string str)))
          (a-program (my-parser (lex-this my-lexer input))))))

(define run
  (lambda (str)
    (value-of-program (scan&parse str))))

;(define str "def f():global a;a = a + 1; print 3;;a = 2;print a; b = f(); print b; print a;")
;(scan&parse str)
;(run str)

