-- Prove2me | solution 1 for ShiTM.counted_loop_transfers_prefix_with_marks
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-16T07:26:11.762642+00:00
-- url     : https://prove2.me/submissions/ef51ead2-7327-4154-9403-1b8a91dc386a

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

open Turing Turing.TM2

/-! ### Bureaucratic `Function.update` normalisation lemmas -/

/-- Collapsing a double update at the same key back to the original function. -/
private theorem shiCl_update_collapse {K : Type} [DecidableEq K] {Gam : K -> Type}
    (ka : K) (T : forall k, List (Gam k)) (a b : List (Gam ka)) (hTa : T ka = b) :
    Function.update (Function.update T ka a) ka b = T := by
  funext k
  by_cases h1 : k = ka
  . subst h1
    simp only [Function.update_self]
    exact hTa.symm
  . simp only [Function.update_of_ne h1]

/-! ### One-`stepAux`-node lemmas (each is `rfl` modulo the popped-cell rewrite) -/

private theorem shiCl_aux_pop {K : Type} [DecidableEq K] {Gam : K -> Type} {Lam sig : Type}
    (k : K) (f : sig -> Option (Gam k) -> sig) (Q : Stmt Gam Lam sig) (v : sig)
    (S : forall j, List (Gam j))
    (y : Gam k) (rst : List (Gam k)) (hS : S k = y :: rst) :
    stepAux (Stmt.pop k f Q) v S = stepAux Q (f v (some y)) (Function.update S k rst) := by
  have h : stepAux (Stmt.pop k f Q) v S
      = stepAux Q (f v (S k).head?) (Function.update S k (S k).tail) := rfl
  rw [h, hS]
  all_goals rfl

private theorem shiCl_aux_branch_true {K : Type} [DecidableEq K] {Gam : K -> Type}
    {Lam sig : Type}
    (g : sig -> Bool) (Q1 Q2 : Stmt Gam Lam sig) (v : sig) (S : forall j, List (Gam j))
    (hg : g v = true) :
    stepAux (Stmt.branch g Q1 Q2) v S = stepAux Q1 v S := by
  have h : stepAux (Stmt.branch g Q1 Q2) v S
      = cond (g v) (stepAux Q1 v S) (stepAux Q2 v S) := rfl
  rw [h, hg]
  all_goals rfl

private theorem shiCl_aux_branch_false {K : Type} [DecidableEq K] {Gam : K -> Type}
    {Lam sig : Type}
    (g : sig -> Bool) (Q1 Q2 : Stmt Gam Lam sig) (v : sig) (S : forall j, List (Gam j))
    (hg : g v = false) :
    stepAux (Stmt.branch g Q1 Q2) v S = stepAux Q2 v S := by
  have h : stepAux (Stmt.branch g Q1 Q2) v S
      = cond (g v) (stepAux Q1 v S) (stepAux Q2 v S) := rfl
  rw [h, hg]
  all_goals rfl

private theorem shiCl_aux_push {K : Type} [DecidableEq K] {Gam : K -> Type} {Lam sig : Type}
    (k : K) (f : sig -> Gam k) (Q : Stmt Gam Lam sig) (v : sig) (S : forall j, List (Gam j)) :
    stepAux (Stmt.push k f Q) v S = stepAux Q v (Function.update S k (f v :: S k)) := rfl

private theorem shiCl_aux_goto {K : Type} [DecidableEq K] {Gam : K -> Type} {Lam sig : Type}
    (fl : sig -> Lam) (v : sig) (S : forall j, List (Gam j)) :
    stepAux (Stmt.goto fl) v S = { l := some (fl v), var := v, stk := S } := rfl

/-! ### The two one-`step` transitions of the counted loop body

Verified against `Turing.TM2.stepAux`
(`Mathlib/Computability/TuringMachine/StackTuringMachine.lean`, the `push`/`pop`/`branch`
equations): `push k f q, v, S => stepAux q v (update S k (f v :: S k))`, i.e. a `push` node
performs its update and hands the *same* `v` on to its continuation.  Hence in the nest

    push kb hpush (push kc hmark (goto fun _ => lc))

`hpush` fires FIRST (on `kb`) and `hmark` fires SECOND (on `kc`), both applied to the SAME
`sig`-value, namely the post-`pop` value `fpop v (some y)`; the resulting stack function is
`update (update (update S ka rst) kb _) kc _`, with the `kc` update OUTERMOST. -/

/-- Continuing iteration: the popped cell passes the test, so the transcoded symbol is pushed
onto `kb`, a counter mark is pushed onto `kc`, and control returns to `lc`. -/
private theorem shiCl_step_cont {K : Type} [DecidableEq K] {Gam : K -> Type} {Lam sig : Type}
    (M : Lam -> Stmt Gam Lam sig) {ka kb kc : K}
    (hab : ka ≠ kb) (hac : ka ≠ kc) (hbc : kb ≠ kc) {lc lnext : Lam}
    {fpop : sig -> Option (Gam ka) -> sig} {gtest : sig -> Bool}
    {hpush : sig -> Gam kb} {hmark : sig -> Gam kc}
    {e : Gam ka -> Gam kb} {mk : Gam ka -> Gam kc}
    (hM : M lc = Stmt.pop ka fpop
            (Stmt.branch gtest
              (Stmt.push kb hpush (Stmt.push kc hmark (Stmt.goto (fun _ => lc))))
              (Stmt.goto (fun _ => lnext))))
    (hval : forall (w : sig) (y : Gam ka), hpush (fpop w (some y)) = e y)
    (hmkv : forall (w : sig) (y : Gam ka), hmark (fpop w (some y)) = mk y)
    (v : sig) (S : forall k, List (Gam k)) (y : Gam ka) (rst : List (Gam ka))
    (hS : S ka = y :: rst) (hg : gtest (fpop v (some y)) = true) :
    step M { l := some lc, var := v, stk := S }
      = some { l := some lc, var := fpop v (some y),
               stk := Function.update
                        (Function.update (Function.update S ka rst) kb (e y :: S kb))
                        kc (mk y :: S kc) } := by
  have h0 : step M { l := some lc, var := v, stk := S } = some (stepAux (M lc) v S) := rfl
  rw [h0, hM, shiCl_aux_pop ka fpop _ v S y rst hS,
    shiCl_aux_branch_true gtest _ _ _ _ hg, shiCl_aux_push, shiCl_aux_push, shiCl_aux_goto,
    hval v y, hmkv v y, Function.update_of_ne (Ne.symm hab) rst S,
    Function.update_of_ne (Ne.symm hbc) (e y :: S kb) (Function.update S ka rst),
    Function.update_of_ne (Ne.symm hac) rst S]
  all_goals rfl

/-- Terminating transition: the popped cell FAILS the test.  It is still consumed (the `pop`
node runs strictly before the `branch` node), it is pushed onto NEITHER `kb` NOR `kc`, and the
remaining tail stays on `ka`. -/
private theorem shiCl_step_stop {K : Type} [DecidableEq K] {Gam : K -> Type} {Lam sig : Type}
    (M : Lam -> Stmt Gam Lam sig) {ka kb kc : K} {lc lnext : Lam}
    {fpop : sig -> Option (Gam ka) -> sig} {gtest : sig -> Bool}
    {hpush : sig -> Gam kb} {hmark : sig -> Gam kc}
    (hM : M lc = Stmt.pop ka fpop
            (Stmt.branch gtest
              (Stmt.push kb hpush (Stmt.push kc hmark (Stmt.goto (fun _ => lc))))
              (Stmt.goto (fun _ => lnext))))
    (v : sig) (S : forall k, List (Gam k)) (c : Gam ka) (t : List (Gam ka))
    (hS : S ka = c :: t) (hg : gtest (fpop v (some c)) = false) :
    step M { l := some lc, var := v, stk := S }
      = some { l := some lnext, var := fpop v (some c), stk := Function.update S ka t } := by
  have h0 : step M { l := some lc, var := v, stk := S } = some (stepAux (M lc) v S) := rfl
  rw [h0, hM, shiCl_aux_pop ka fpop _ v S c t hS,
    shiCl_aux_branch_false gtest _ _ _ _ hg, shiCl_aux_goto]
  all_goals rfl

/-! ### The loop-induction core: consume a whole passing prefix, counting on `kc` -/

private theorem shiCl_loop_core {K : Type} [DecidableEq K] {Gam : K -> Type} {Lam sig : Type}
    (M : Lam -> Stmt Gam Lam sig) {ka kb kc : K}
    (hab : ka ≠ kb) (hac : ka ≠ kc) (hbc : kb ≠ kc) {lc lnext : Lam}
    {fpop : sig -> Option (Gam ka) -> sig} {gtest : sig -> Bool}
    {hpush : sig -> Gam kb} {hmark : sig -> Gam kc}
    {e : Gam ka -> Gam kb} {mk : Gam ka -> Gam kc}
    (hM : M lc = Stmt.pop ka fpop
            (Stmt.branch gtest
              (Stmt.push kb hpush (Stmt.push kc hmark (Stmt.goto (fun _ => lc))))
              (Stmt.goto (fun _ => lnext))))
    (hval : forall (w : sig) (y : Gam ka), hpush (fpop w (some y)) = e y)
    (hmkv : forall (w : sig) (y : Gam ka), hmark (fpop w (some y)) = mk y) :
    forall (p : List (Gam ka)),
      (forall (w : sig) (y : Gam ka), y ∈ p -> gtest (fpop w (some y)) = true) ->
      forall (v : sig) (S T : forall k, List (Gam k)) (rest : List (Gam ka)),
        S ka = p ++ rest -> T ka = rest -> T kb = (List.map e p).reverse ++ S kb ->
        T kc = (List.map mk p).reverse ++ S kc ->
        (forall k, k ≠ ka -> k ≠ kb -> k ≠ kc -> T k = S k) ->
        (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[p.length]
            (some { l := some lc, var := v, stk := S })
          = some { l := some lc, var := List.foldl (fun w y => fpop w (some y)) v p,
                   stk := T } := by
  intro p
  induction p with
  | nil =>
    intro _ v S T rest hS hTa hTb hTc hTo
    have hST : T = S := by
      funext k
      by_cases h1 : k = ka
      . subst h1
        rw [hTa, hS, List.nil_append]
      . by_cases h2 : k = kb
        . subst h2
          rw [hTb]
          simp
        . by_cases h3 : k = kc
          . subst h3
            rw [hTc]
            simp
          . exact hTo k h1 h2 h3
    rw [hST]
    all_goals rfl
  | cons y p ih =>
    intro hp v S T rest hS hTa hTb hTc hTo
    have hy : gtest (fpop v (some y)) = true := hp v y (List.mem_cons.mpr (Or.inl rfl))
    have hSy : S ka = y :: (p ++ rest) := hS
    have h1 : step M { l := some lc, var := v, stk := S }
        = some { l := some lc, var := fpop v (some y),
                 stk := Function.update
                          (Function.update (Function.update S ka (p ++ rest)) kb
                            (e y :: S kb)) kc (mk y :: S kc) } :=
      shiCl_step_cont M hab hac hbc hM hval hmkv v S y (p ++ rest) hSy hy
    have hS1a : (Function.update
        (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb))
        kc (mk y :: S kc)) ka = p ++ rest := by
      simp only [Function.update_of_ne hac, Function.update_of_ne hab, Function.update_self]
    have hS1b : (Function.update
        (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb))
        kc (mk y :: S kc)) kb = e y :: S kb := by
      simp only [Function.update_of_ne hbc, Function.update_self]
    have hS1c : (Function.update
        (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb))
        kc (mk y :: S kc)) kc = mk y :: S kc := by
      simp only [Function.update_self]
    have hS1o : forall k, k ≠ ka -> k ≠ kb -> k ≠ kc -> (Function.update
        (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb))
        kc (mk y :: S kc)) k = S k := by
      intro k h1' h2' h3'
      simp only [Function.update_of_ne h3', Function.update_of_ne h2',
        Function.update_of_ne h1']
    have hTb' : T kb = (List.map e p).reverse ++ (Function.update
        (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb))
        kc (mk y :: S kc)) kb := by
      rw [hS1b, hTb]
      simp
    have hTc' : T kc = (List.map mk p).reverse ++ (Function.update
        (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb))
        kc (mk y :: S kc)) kc := by
      rw [hS1c, hTc]
      simp
    have hTo' : forall k, k ≠ ka -> k ≠ kb -> k ≠ kc -> T k = (Function.update
        (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb))
        kc (mk y :: S kc)) k := by
      intro k h1' h2' h3'
      rw [hTo k h1' h2' h3', hS1o k h1' h2' h3']
    have h2 := ih (fun w z hz => hp w z (List.mem_cons.mpr (Or.inr hz))) (fpop v (some y))
      (Function.update
        (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb))
        kc (mk y :: S kc)) T rest hS1a hTa hTb' hTc' hTo'
    have hstep : (some { l := some lc, var := v, stk := S } : Option (Cfg Gam Lam sig)).bind
        (step M)
        = some { l := some lc, var := fpop v (some y),
                 stk := Function.update
                          (Function.update (Function.update S ka (p ++ rest)) kb
                            (e y :: S kb)) kc (mk y :: S kc) } := h1
    have hfin : (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[p.length + 1]
        (some { l := some lc, var := v, stk := S })
        = some { l := some lc,
                 var := List.foldl (fun w z => fpop w (some z)) (fpop v (some y)) p,
                 stk := T } := by
      rw [Function.iterate_succ_apply, hstep]
      exact h2
    exact hfin

/-! ### Prefix + distinguished symbol, with an abstract target stack -/

private theorem shiCl_loop_full {K : Type} [DecidableEq K] {Gam : K -> Type} {Lam sig : Type}
    (M : Lam -> Stmt Gam Lam sig) {ka kb kc : K}
    (hab : ka ≠ kb) (hac : ka ≠ kc) (hbc : kb ≠ kc) {lc lnext : Lam}
    {fpop : sig -> Option (Gam ka) -> sig} {gtest : sig -> Bool}
    {hpush : sig -> Gam kb} {hmark : sig -> Gam kc}
    {e : Gam ka -> Gam kb} {mk : Gam ka -> Gam kc}
    (hM : M lc = Stmt.pop ka fpop
            (Stmt.branch gtest
              (Stmt.push kb hpush (Stmt.push kc hmark (Stmt.goto (fun _ => lc))))
              (Stmt.goto (fun _ => lnext))))
    (hval : forall (w : sig) (y : Gam ka), hpush (fpop w (some y)) = e y)
    (hmkv : forall (w : sig) (y : Gam ka), hmark (fpop w (some y)) = mk y)
    (p : List (Gam ka))
    (hcont : forall (w : sig) (y : Gam ka), y ∈ p -> gtest (fpop w (some y)) = true)
    (c : Gam ka) (hstop : forall w : sig, gtest (fpop w (some c)) = false) (t : List (Gam ka))
    (v : sig) (S T : forall k, List (Gam k)) (hS : S ka = p ++ c :: t) (hTa : T ka = t)
    (hTb : T kb = (List.map e p).reverse ++ S kb)
    (hTc : T kc = (List.map mk p).reverse ++ S kc)
    (hTo : forall k, k ≠ ka -> k ≠ kb -> k ≠ kc -> T k = S k) :
    (fun cf : Option (Cfg Gam Lam sig) => cf.bind (step M))^[p.length + 1]
        (some { l := some lc, var := v, stk := S })
      = some { l := some lnext,
               var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
               stk := T } := by
  have hT1a : (Function.update T ka (c :: t)) ka = c :: t := Function.update_self ka (c :: t) T
  have hT1b : (Function.update T ka (c :: t)) kb = (List.map e p).reverse ++ S kb := by
    rw [Function.update_of_ne (Ne.symm hab) (c :: t) T, hTb]
  have hT1c : (Function.update T ka (c :: t)) kc = (List.map mk p).reverse ++ S kc := by
    rw [Function.update_of_ne (Ne.symm hac) (c :: t) T, hTc]
  have hT1o : forall k, k ≠ ka -> k ≠ kb -> k ≠ kc ->
      (Function.update T ka (c :: t)) k = S k := by
    intro k h1' h2' h3'
    rw [Function.update_of_ne h1' (c :: t) T, hTo k h1' h2' h3']
  have hcore := shiCl_loop_core M hab hac hbc hM hval hmkv p hcont v S
    (Function.update T ka (c :: t)) (c :: t) hS hT1a hT1b hT1c hT1o
  have hlast' :
      step M { l := some lc,
               var := List.foldl (fun w y => fpop w (some y)) v p,
               stk := Function.update T ka (c :: t) }
        = some { l := some lnext,
                   var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
                   stk := T } := by
    rw [shiCl_step_stop M hM
        (List.foldl (fun w y => fpop w (some y)) v p)
        (Function.update T ka (c :: t)) c t hT1a
        (hstop (List.foldl (fun w y => fpop w (some y)) v p)),
      shiCl_update_collapse ka T (c :: t) t hTa]
  rw [Function.iterate_succ_apply', hcore]
  exact hlast'

/-! ### The public statement -/

/-- **Counted (three-stack) loop induction for `Turing.TM2`.**

For an arbitrary machine `M` whose label `lc` runs the body

    pop ka fpop
      (branch gtest
        (push kb hpush (push kc hmark (goto fun _ => lc)))
        (goto fun _ => lnext))

with `ka`, `kb`, `kc` pairwise distinct, the loop consumes a prefix `p` of stack `ka` all of
whose cells make the popped test succeed, transcoding each cell onto `kb` via `e` AND laying
down one counter mark on `kc` via `mk`, and then consumes ONE further cell `c` that makes the
test fail.  Verified against `Turing.TM2.stepAux`:

* a `push` node performs its stack update and passes the SAME `sig`-value to its continuation,
  so `hpush` and `hmark` are both applied to the post-`pop` value; `hpush` fires first and the
  `kc` update ends up OUTERMOST;
* the `pop` node runs strictly BEFORE the `branch` node, so the distinguished symbol `c` is
  popped (removed from `ka`) even on the failing branch, its `fpop` update IS applied, and it
  is pushed onto neither `kb` nor `kc`;
* the tail `t` after `c` is left untouched on `ka`, and every stack other than `ka`, `kb`, `kc`
  is untouched;
* the run takes EXACTLY `p.length + 1` steps.

The third conjunct reads the counter as a NUMBER: stack `kc` has grown by exactly `p.length`.
The fourth conjunct gives the `List.replicate` normal form in the case downstream actually
uses, namely a constant mark `mk = fun _ => m`. -/
theorem solution {K : Type} [DecidableEq K] {Gam : K → Type} {Lam sig : Type}
    (M : Lam → Turing.TM2.Stmt Gam Lam sig) {ka kb kc : K}
    (hab : ka ≠ kb) (hac : ka ≠ kc) (hbc : kb ≠ kc) {lc lnext : Lam}
    {fpop : sig → Option (Gam ka) → sig} {gtest : sig → Bool}
    {hpush : sig → Gam kb} {hmark : sig → Gam kc}
    {e : Gam ka → Gam kb} {mk : Gam ka → Gam kc}
    (hM : M lc = Turing.TM2.Stmt.pop ka fpop
            (Turing.TM2.Stmt.branch gtest
              (Turing.TM2.Stmt.push kb hpush
                (Turing.TM2.Stmt.push kc hmark (Turing.TM2.Stmt.goto (fun _ => lc))))
              (Turing.TM2.Stmt.goto (fun _ => lnext))))
    (hval : forall (w : sig) (y : Gam ka), hpush (fpop w (some y)) = e y)
    (hmkv : forall (w : sig) (y : Gam ka), hmark (fpop w (some y)) = mk y)
    (p : List (Gam ka))
    (hcont : forall (w : sig) (y : Gam ka), y ∈ p → gtest (fpop w (some y)) = true)
    (c : Gam ka) (hstop : forall w : sig, gtest (fpop w (some c)) = false) (t : List (Gam ka))
    (v : sig) (S : forall k, List (Gam k)) (hS : S ka = p ++ c :: t) :
    (fun cf : Option (Turing.TM2.Cfg Gam Lam sig) => cf.bind (Turing.TM2.step M))^[p.length + 1]
        (some { l := some lc, var := v, stk := S })
      = some { l := some lnext,
               var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
               stk := Function.update
                        (Function.update (Function.update S ka t) kb
                          ((List.map e p).reverse ++ S kb))
                        kc ((List.map mk p).reverse ++ S kc) }
    ∧ Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step M)
        { l := some lc, var := v, stk := S }
        (some { l := some lnext,
                var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
                stk := Function.update
                         (Function.update (Function.update S ka t) kb
                           ((List.map e p).reverse ++ S kb))
                         kc ((List.map mk p).reverse ++ S kc) })
        (p.length + 1))
    ∧ ((List.map mk p).reverse ++ S kc).length = p.length + (S kc).length
    ∧ (forall m : Gam kc, (forall y : Gam ka, mk y = m) →
          (List.map mk p).reverse ++ S kc = List.replicate p.length m ++ S kc) := by
  have hTa : (Function.update
      (Function.update (Function.update S ka t) kb ((List.map e p).reverse ++ S kb))
      kc ((List.map mk p).reverse ++ S kc)) ka = t := by
    simp only [Function.update_of_ne hac, Function.update_of_ne hab, Function.update_self]
  have hTb : (Function.update
      (Function.update (Function.update S ka t) kb ((List.map e p).reverse ++ S kb))
      kc ((List.map mk p).reverse ++ S kc)) kb = (List.map e p).reverse ++ S kb := by
    simp only [Function.update_of_ne hbc, Function.update_self]
  have hTc : (Function.update
      (Function.update (Function.update S ka t) kb ((List.map e p).reverse ++ S kb))
      kc ((List.map mk p).reverse ++ S kc)) kc = (List.map mk p).reverse ++ S kc := by
    simp only [Function.update_self]
  have hTo : forall k, k ≠ ka → k ≠ kb → k ≠ kc → (Function.update
      (Function.update (Function.update S ka t) kb ((List.map e p).reverse ++ S kb))
      kc ((List.map mk p).reverse ++ S kc)) k = S k := by
    intro k h1' h2' h3'
    simp only [Function.update_of_ne h3', Function.update_of_ne h2',
      Function.update_of_ne h1']
  have hkey := shiCl_loop_full M hab hac hbc hM hval hmkv p hcont c hstop t v S
    (Function.update
      (Function.update (Function.update S ka t) kb ((List.map e p).reverse ++ S kb))
      kc ((List.map mk p).reverse ++ S kc))
    hS hTa hTb hTc hTo
  refine ⟨hkey, ⟨⟨p.length + 1, hkey⟩, le_refl _⟩, ?_, ?_⟩
  . rw [List.length_append, List.length_reverse, List.length_map]
  . intro m hm
    have h1 : mk = fun _ => m := funext hm
    rw [h1, List.map_const', List.reverse_replicate]
