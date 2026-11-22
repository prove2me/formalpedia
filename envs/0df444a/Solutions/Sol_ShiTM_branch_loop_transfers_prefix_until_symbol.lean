-- Prove2me | solution 1 for ShiTM.branch_loop_transfers_prefix_until_symbol
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-16T07:06:07.456996+00:00
-- url     : https://prove2.me/submissions/7c2def0d-efe3-4cf0-95f3-b420125b907f

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

open Turing Turing.TM2

/-! ### Bureaucratic `Function.update` normalisation lemmas -/

/-- Collapsing a double update at the same key back to the original function. -/
private theorem shiLp_update_collapse {K : Type} [DecidableEq K] {Γ : K → Type}
    (ka : K) (T : ∀ k, List (Γ k)) (a b : List (Γ ka)) (hTa : T ka = b) :
    Function.update (Function.update T ka a) ka b = T := by
  funext k
  by_cases h1 : k = ka
  · subst h1
    simp only [Function.update_self]
    exact hTa.symm
  · simp only [Function.update_of_ne h1]

/-! ### One-`stepAux`-node lemmas (each is `rfl` modulo the popped-cell rewrite) -/

private theorem shiLp_aux_pop {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (k : K) (f : σ → Option (Γ k) → σ) (Q : Stmt Γ Λ σ) (v : σ) (S : ∀ j, List (Γ j))
    (y : Γ k) (rst : List (Γ k)) (hS : S k = y :: rst) :
    stepAux (Stmt.pop k f Q) v S = stepAux Q (f v (some y)) (Function.update S k rst) := by
  have h : stepAux (Stmt.pop k f Q) v S
      = stepAux Q (f v (S k).head?) (Function.update S k (S k).tail) := rfl
  rw [h, hS]
  all_goals rfl

private theorem shiLp_aux_branch_true {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (g : σ → Bool) (Q₁ Q₂ : Stmt Γ Λ σ) (v : σ) (S : ∀ j, List (Γ j)) (hg : g v = true) :
    stepAux (Stmt.branch g Q₁ Q₂) v S = stepAux Q₁ v S := by
  have h : stepAux (Stmt.branch g Q₁ Q₂) v S
      = cond (g v) (stepAux Q₁ v S) (stepAux Q₂ v S) := rfl
  rw [h, hg]
  all_goals rfl

private theorem shiLp_aux_branch_false {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (g : σ → Bool) (Q₁ Q₂ : Stmt Γ Λ σ) (v : σ) (S : ∀ j, List (Γ j)) (hg : g v = false) :
    stepAux (Stmt.branch g Q₁ Q₂) v S = stepAux Q₂ v S := by
  have h : stepAux (Stmt.branch g Q₁ Q₂) v S
      = cond (g v) (stepAux Q₁ v S) (stepAux Q₂ v S) := rfl
  rw [h, hg]
  all_goals rfl

private theorem shiLp_aux_push {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (k : K) (f : σ → Γ k) (Q : Stmt Γ Λ σ) (v : σ) (S : ∀ j, List (Γ j)) :
    stepAux (Stmt.push k f Q) v S = stepAux Q v (Function.update S k (f v :: S k)) := rfl

private theorem shiLp_aux_goto {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (fl : σ → Λ) (v : σ) (S : ∀ j, List (Γ j)) :
    stepAux (Stmt.goto fl) v S = { l := some (fl v), var := v, stk := S } := rfl

/-! ### The two one-`step` transitions of the loop body -/

/-- Continuing iteration: the popped cell passes the test, so it is pushed (transcoded) onto
`kb` and control returns to `lc`. -/
private theorem shiLp_step_cont {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) {ka kb : K} (hab : ka ≠ kb) {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool} {hpush : σ → Γ kb} {e : Γ ka → Γ kb}
    (hM : M lc = Stmt.pop ka fpop
            (Stmt.branch gtest
              (Stmt.push kb hpush (Stmt.goto (fun _ => lc)))
              (Stmt.goto (fun _ => lnext))))
    (hval : ∀ (w : σ) (y : Γ ka), hpush (fpop w (some y)) = e y)
    (v : σ) (S : ∀ k, List (Γ k)) (y : Γ ka) (rst : List (Γ ka)) (hS : S ka = y :: rst)
    (hg : gtest (fpop v (some y)) = true) :
    step M { l := some lc, var := v, stk := S }
      = some { l := some lc, var := fpop v (some y),
               stk := Function.update (Function.update S ka rst) kb (e y :: S kb) } := by
  have h0 : step M { l := some lc, var := v, stk := S } = some (stepAux (M lc) v S) := rfl
  rw [h0, hM, shiLp_aux_pop ka fpop _ v S y rst hS,
    shiLp_aux_branch_true gtest _ _ _ _ hg, shiLp_aux_push, shiLp_aux_goto,
    Function.update_of_ne (Ne.symm hab) rst S, hval v y]
  all_goals rfl

/-- Terminating transition: the popped cell FAILS the test.  It is still consumed (the `pop`
node runs before the `branch` node), it is NOT pushed onto `kb`, and the remaining tail stays
on `ka`. -/
private theorem shiLp_step_stop {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) {ka kb : K} {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool} {hpush : σ → Γ kb}
    (hM : M lc = Stmt.pop ka fpop
            (Stmt.branch gtest
              (Stmt.push kb hpush (Stmt.goto (fun _ => lc)))
              (Stmt.goto (fun _ => lnext))))
    (v : σ) (S : ∀ k, List (Γ k)) (c : Γ ka) (t : List (Γ ka)) (hS : S ka = c :: t)
    (hg : gtest (fpop v (some c)) = false) :
    step M { l := some lc, var := v, stk := S }
      = some { l := some lnext, var := fpop v (some c), stk := Function.update S ka t } := by
  have h0 : step M { l := some lc, var := v, stk := S } = some (stepAux (M lc) v S) := rfl
  rw [h0, hM, shiLp_aux_pop ka fpop _ v S c t hS,
    shiLp_aux_branch_false gtest _ _ _ _ hg, shiLp_aux_goto]
  all_goals rfl

/-! ### The loop-induction core: consume a whole passing prefix -/

private theorem shiLp_loop_core {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) {ka kb : K} (hab : ka ≠ kb) {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool} {hpush : σ → Γ kb} {e : Γ ka → Γ kb}
    (hM : M lc = Stmt.pop ka fpop
            (Stmt.branch gtest
              (Stmt.push kb hpush (Stmt.goto (fun _ => lc)))
              (Stmt.goto (fun _ => lnext))))
    (hval : ∀ (w : σ) (y : Γ ka), hpush (fpop w (some y)) = e y) :
    ∀ (p : List (Γ ka)), (∀ (w : σ) (y : Γ ka), y ∈ p → gtest (fpop w (some y)) = true) →
      ∀ (v : σ) (S T : ∀ k, List (Γ k)) (rest : List (Γ ka)),
        S ka = p ++ rest → T ka = rest → T kb = (List.map e p).reverse ++ S kb →
        (∀ k, k ≠ ka → k ≠ kb → T k = S k) →
        (fun cf : Option (Cfg Γ Λ σ) => cf.bind (step M))^[p.length]
            (some { l := some lc, var := v, stk := S })
          = some { l := some lc, var := List.foldl (fun w y => fpop w (some y)) v p,
                   stk := T } := by
  intro p
  induction p with
  | nil =>
    intro _ v S T rest hS hTa hTb hTo
    have hST : T = S := by
      funext k
      by_cases h1 : k = ka
      · subst h1
        rw [hTa, hS, List.nil_append]
      · by_cases h2 : k = kb
        · subst h2
          rw [hTb]
          simp
        · exact hTo k h1 h2
    rw [hST]
    all_goals rfl
  | cons y p ih =>
    intro hp v S T rest hS hTa hTb hTo
    have hy : gtest (fpop v (some y)) = true := hp v y (List.mem_cons.mpr (Or.inl rfl))
    have hSy : S ka = y :: (p ++ rest) := hS
    have h1 : step M { l := some lc, var := v, stk := S }
        = some { l := some lc, var := fpop v (some y),
                 stk := Function.update (Function.update S ka (p ++ rest)) kb
                          (e y :: S kb) } :=
      shiLp_step_cont M hab hM hval v S y (p ++ rest) hSy hy
    have hS1a : (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb)) ka
        = p ++ rest := by
      simp only [Function.update_of_ne hab, Function.update_self]
    have hS1b : (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb)) kb
        = e y :: S kb := by
      simp only [Function.update_self]
    have hS1o : ∀ k, k ≠ ka → k ≠ kb →
        (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb)) k = S k := by
      intro k h1' h2'
      simp only [Function.update_of_ne h1', Function.update_of_ne h2']
    have hTb' : T kb = (List.map e p).reverse
        ++ (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb)) kb := by
      rw [hS1b, hTb]
      simp
    have hTo' : ∀ k, k ≠ ka → k ≠ kb →
        T k = (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb)) k := by
      intro k h1' h2'
      rw [hTo k h1' h2', hS1o k h1' h2']
    have h2 := ih (fun w z hz => hp w z (List.mem_cons.mpr (Or.inr hz))) (fpop v (some y))
      (Function.update (Function.update S ka (p ++ rest)) kb (e y :: S kb)) T rest
      hS1a hTa hTb' hTo'
    have hstep : (some { l := some lc, var := v, stk := S } : Option (Cfg Γ Λ σ)).bind (step M)
        = some { l := some lc, var := fpop v (some y),
                 stk := Function.update (Function.update S ka (p ++ rest)) kb
                          (e y :: S kb) } := h1
    have hfin : (fun cf : Option (Cfg Γ Λ σ) => cf.bind (step M))^[p.length + 1]
        (some { l := some lc, var := v, stk := S })
        = some { l := some lc,
                 var := List.foldl (fun w z => fpop w (some z)) (fpop v (some y)) p,
                 stk := T } := by
      rw [Function.iterate_succ_apply, hstep]
      exact h2
    exact hfin

/-! ### Prefix + distinguished symbol, with an abstract target stack -/

private theorem shiLp_loop_full {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Stmt Γ Λ σ) {ka kb : K} (hab : ka ≠ kb) {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool} {hpush : σ → Γ kb} {e : Γ ka → Γ kb}
    (hM : M lc = Stmt.pop ka fpop
            (Stmt.branch gtest
              (Stmt.push kb hpush (Stmt.goto (fun _ => lc)))
              (Stmt.goto (fun _ => lnext))))
    (hval : ∀ (w : σ) (y : Γ ka), hpush (fpop w (some y)) = e y)
    (p : List (Γ ka)) (hcont : ∀ (w : σ) (y : Γ ka), y ∈ p → gtest (fpop w (some y)) = true)
    (c : Γ ka) (hstop : ∀ w : σ, gtest (fpop w (some c)) = false) (t : List (Γ ka))
    (v : σ) (S T : ∀ k, List (Γ k)) (hS : S ka = p ++ c :: t) (hTa : T ka = t)
    (hTb : T kb = (List.map e p).reverse ++ S kb)
    (hTo : ∀ k, k ≠ ka → k ≠ kb → T k = S k) :
    (fun cf : Option (Cfg Γ Λ σ) => cf.bind (step M))^[p.length + 1]
        (some { l := some lc, var := v, stk := S })
      = some { l := some lnext,
               var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
               stk := T } := by
  have hT1a : (Function.update T ka (c :: t)) ka = c :: t := Function.update_self ka (c :: t) T
  have hT1b : (Function.update T ka (c :: t)) kb = (List.map e p).reverse ++ S kb := by
    rw [Function.update_of_ne (Ne.symm hab) (c :: t) T, hTb]
  have hT1o : ∀ k, k ≠ ka → k ≠ kb → (Function.update T ka (c :: t)) k = S k := by
    intro k h1' h2'
    rw [Function.update_of_ne h1' (c :: t) T, hTo k h1' h2']
  have hcore := shiLp_loop_core M hab hM hval p hcont v S (Function.update T ka (c :: t))
    (c :: t) hS hT1a hT1b hT1o
  have hlast' :
      step M { l := some lc,
               var := List.foldl (fun w y => fpop w (some y)) v p,
               stk := Function.update T ka (c :: t) }
        = some { l := some lnext,
                   var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
                   stk := T } := by
    rw [shiLp_step_stop M hM (List.foldl (fun w y => fpop w (some y)) v p)
        (Function.update T ka (c :: t)) c t hT1a
        (hstop (List.foldl (fun w y => fpop w (some y)) v p)),
      shiLp_update_collapse ka T (c :: t) t hTa]
  rw [Function.iterate_succ_apply', hcore]
  exact hlast'

/-! ### The public statement -/

/-- **Symbol-branching loop induction for `Turing.TM2`.**

For an arbitrary machine `M` whose label `lc` runs the body

    pop ka fpop (branch gtest (push kb hpush (goto fun _ => lc)) (goto fun _ => lnext))

the loop consumes a prefix `p` of stack `ka` all of whose cells make the popped test succeed,
transcoding each cell onto stack `kb` via `e`, and then consumes ONE further cell `c` that makes
the test fail.  Verified against `Turing.TM2.stepAux`:

* the `pop` node runs BEFORE the `branch` node, so the distinguished symbol `c` is popped
  (removed from `ka`) even on the failing branch, and it is NOT pushed onto `kb`;
* the tail `t` after `c` is left untouched on `ka`;
* the final `var` is `fpop (p.foldl (fun w y => fpop w (some y)) v) (some c)`, i.e. the
  distinguished symbol's own `fpop` update IS applied. -/
theorem solution {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) {ka kb : K} (hab : ka ≠ kb) {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool} {hpush : σ → Γ kb} {e : Γ ka → Γ kb}
    (hM : M lc = Turing.TM2.Stmt.pop ka fpop
            (Turing.TM2.Stmt.branch gtest
              (Turing.TM2.Stmt.push kb hpush (Turing.TM2.Stmt.goto (fun _ => lc)))
              (Turing.TM2.Stmt.goto (fun _ => lnext))))
    (hval : ∀ (w : σ) (y : Γ ka), hpush (fpop w (some y)) = e y)
    (p : List (Γ ka)) (hcont : ∀ (w : σ) (y : Γ ka), y ∈ p → gtest (fpop w (some y)) = true)
    (c : Γ ka) (hstop : ∀ w : σ, gtest (fpop w (some c)) = false) (t : List (Γ ka))
    (v : σ) (S : ∀ k, List (Γ k)) (hS : S ka = p ++ c :: t) :
    (fun cf : Option (Turing.TM2.Cfg Γ Λ σ) => cf.bind (Turing.TM2.step M))^[p.length + 1]
        (some { l := some lc, var := v, stk := S })
      = some { l := some lnext,
               var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
               stk := Function.update (Function.update S ka t) kb
                        ((List.map e p).reverse ++ S kb) }
    ∧ Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step M)
        { l := some lc, var := v, stk := S }
        (some { l := some lnext,
                var := fpop (List.foldl (fun w y => fpop w (some y)) v p) (some c),
                stk := Function.update (Function.update S ka t) kb
                         ((List.map e p).reverse ++ S kb) })
        (p.length + 1)) := by
  have hTa : (Function.update (Function.update S ka t) kb
      ((List.map e p).reverse ++ S kb)) ka = t := by
    simp only [Function.update_of_ne hab, Function.update_self]
  have hTb : (Function.update (Function.update S ka t) kb
      ((List.map e p).reverse ++ S kb)) kb = (List.map e p).reverse ++ S kb := by
    simp only [Function.update_self]
  have hTo : ∀ k, k ≠ ka → k ≠ kb → (Function.update (Function.update S ka t) kb
      ((List.map e p).reverse ++ S kb)) k = S k := by
    intro k h1' h2'
    simp only [Function.update_of_ne h1', Function.update_of_ne h2']
  have hkey := shiLp_loop_full M hab hM hval p hcont c hstop t v S
    (Function.update (Function.update S ka t) kb ((List.map e p).reverse ++ S kb))
    hS hTa hTb hTo
  exact ⟨hkey, ⟨⟨p.length + 1, hkey⟩, le_refl _⟩⟩
