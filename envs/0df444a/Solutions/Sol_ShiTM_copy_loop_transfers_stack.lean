-- Prove2me | solution 1 for ShiTM.copy_loop_transfers_stack
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T18:45:02.02268+00:00
-- url     : https://prove2.me/submissions/7cf41e64-c5f5-4365-8979-dc57c07ad81f

import Mathlib.Computability.TuringMachine.Computable

set_option autoImplicit false

/-!
# The TM2 one-stack-to-another transfer loop (the "copy phase")

To sequence two `TM2` machines one must move the output stack of the first onto the input
stack of the second.  A machine does this with a tight loop at a designated label `lc` whose
statement is

  `pop ka fpop (branch gtest (push kb hpush (goto fun _ => lc)) (goto fun _ => lnext))`

that is: pop the source stack `ka` into the internal state, test whether anything came out,
and if so push it onto the target stack `kb` and jump back to `lc`; otherwise fall through
to `lnext`.  Because `Turing.TM2.stepAux` recurses through an *entire* `Stmt` tree inside a
single `Turing.TM2.step`, one pass of this loop costs exactly one step per element plus one
final step to observe the empty stack: `s.length + 1` steps in total.

`solution` states this in two equivalent ways at once:

* as an explicit `s.length + 1`-fold iteration of the option-lifted step function, which is
  literally the `evals_in_steps` field of `StateTransition.EvalsTo`; and
* packaged as `StateTransition.EvalsToInTime` with time bound `s.length + 1`, ready to be
  chained with `StateTransition.EvalsToInTime.trans`.

The lemma is honest about reversal: popping and pushing reverses, so the target stack ends up
holding `(s.map e).reverse ++ t` where `t` is its previous content.  A caller who needs `s`
in its original order composes two instances of this lemma through a scratch stack, for a
total of `2 * s.length + 2` steps.  The map `e : Γ ka → Γ kb` is the alphabet identification
between the two stacks (`e = id` in the identity-encoding case); it is what makes the
statement typecheck when `Γ ka` and `Γ kb` are literally different types.
-/

/-- Two successive `Function.update`s, at `ka` and then at `kb`, destroy all information about
the underlying dependent function at `ka` and at `kb`.  Hence two functions that agree away
from `ka` and `kb` become equal after such a pair of updates. -/
private theorem shiCopy_update_two_eq {K : Type} [DecidableEq K] {Γ : K → Type}
    (ka kb : K) (S T : ∀ k, List (Γ k))
    (h : ∀ k, k ≠ ka → k ≠ kb → S k = T k)
    (u : List (Γ ka)) (w : List (Γ kb)) :
    Function.update (Function.update S ka u) kb w
      = Function.update (Function.update T ka u) kb w := by
  funext k
  by_cases hk : k = kb
  · subst hk
    rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]
    by_cases hk2 : k = ka
    · subst hk2
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hk2, Function.update_of_ne hk2]
      exact h k hk2 hk

/-- One `Turing.TM2.step` of the copy loop when the source stack `ka` is nonempty: the head is
moved (through the internal state) onto the target stack `kb`, and control returns to `lc`. -/
private theorem shiCopy_step_cons {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) {ka kb : K} (hab : ka ≠ kb) {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool} {hpush : σ → Γ kb} {e : Γ ka → Γ kb}
    (hM : M lc = Turing.TM2.Stmt.pop ka fpop
            (Turing.TM2.Stmt.branch gtest
              (Turing.TM2.Stmt.push kb hpush (Turing.TM2.Stmt.goto (fun _ => lc)))
              (Turing.TM2.Stmt.goto (fun _ => lnext))))
    (hcont : ∀ (w : σ) (y : Γ ka), gtest (fpop w (some y)) = true)
    (hval : ∀ (w : σ) (y : Γ ka), hpush (fpop w (some y)) = e y)
    (x : Γ ka) (s' : List (Γ ka)) (v : σ) (S : ∀ k, List (Γ k)) (hS : S ka = x :: s') :
    Turing.TM2.step M { l := some lc, var := v, stk := S }
      = some { l := some lc, var := fpop v (some x),
               stk := Function.update (Function.update S ka s') kb (e x :: S kb) } := by
  have hstep : Turing.TM2.step M { l := some lc, var := v, stk := S }
      = some (Turing.TM2.stepAux (M lc) v S) := by
    first
      | (rfl; done)
      | (simp only [Turing.TM2.step.eq_2]; done)
      | (simp [Turing.TM2.step]; done)
  rw [hstep, hM]
  first
    | (simp only [Turing.TM2.stepAux.eq_1, Turing.TM2.stepAux.eq_3, Turing.TM2.stepAux.eq_5,
        Turing.TM2.stepAux.eq_6, hS, List.head?_cons, List.tail_cons, hcont, cond_true, hval,
        Function.update_of_ne (Ne.symm hab)]; done)
    | (simp only [Turing.TM2.stepAux.eq_1, Turing.TM2.stepAux.eq_3, Turing.TM2.stepAux.eq_5,
        Turing.TM2.stepAux.eq_6, hS, List.head?_cons, List.tail_cons, hcont, cond_true, hval,
        Function.update_of_ne (Ne.symm hab)]; rfl; done)
    | (simp [Turing.TM2.stepAux, hS, hcont, hval, Function.update_of_ne (Ne.symm hab)]; done)

/-- One `Turing.TM2.step` of the copy loop when the source stack `ka` is empty: the loop falls
through to `lnext`, leaving the stacks alone (the `pop` of an empty stack is a no-op). -/
private theorem shiCopy_step_nil {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) {ka kb : K} {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool} {hpush : σ → Γ kb}
    (hM : M lc = Turing.TM2.Stmt.pop ka fpop
            (Turing.TM2.Stmt.branch gtest
              (Turing.TM2.Stmt.push kb hpush (Turing.TM2.Stmt.goto (fun _ => lc)))
              (Turing.TM2.Stmt.goto (fun _ => lnext))))
    (hstop : ∀ w : σ, gtest (fpop w none) = false)
    (v : σ) (S : ∀ k, List (Γ k)) (hS : S ka = []) :
    Turing.TM2.step M { l := some lc, var := v, stk := S }
      = some { l := some lnext, var := fpop v none, stk := Function.update S ka [] } := by
  have hstep : Turing.TM2.step M { l := some lc, var := v, stk := S }
      = some (Turing.TM2.stepAux (M lc) v S) := by
    first
      | (rfl; done)
      | (simp only [Turing.TM2.step.eq_2]; done)
      | (simp [Turing.TM2.step]; done)
  rw [hstep, hM]
  first
    | (simp only [Turing.TM2.stepAux.eq_3, Turing.TM2.stepAux.eq_5, Turing.TM2.stepAux.eq_6,
        hS, List.head?_nil, List.tail_nil, hstop, cond_false]; done)
    | (simp only [Turing.TM2.stepAux.eq_3, Turing.TM2.stepAux.eq_5, Turing.TM2.stepAux.eq_6,
        hS, List.head?_nil, List.tail_nil, hstop, cond_false]; rfl; done)
    | (simp [Turing.TM2.stepAux, hS, hstop]; done)

/-- The transfer loop, by induction on the source stack.  `v` and `S` must be generalised for
the induction, hence the `∀` in the conclusion. -/
private theorem shiCopy_iter {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) {ka kb : K} (hab : ka ≠ kb) {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool} {hpush : σ → Γ kb} {e : Γ ka → Γ kb}
    (hM : M lc = Turing.TM2.Stmt.pop ka fpop
            (Turing.TM2.Stmt.branch gtest
              (Turing.TM2.Stmt.push kb hpush (Turing.TM2.Stmt.goto (fun _ => lc)))
              (Turing.TM2.Stmt.goto (fun _ => lnext))))
    (hcont : ∀ (w : σ) (y : Γ ka), gtest (fpop w (some y)) = true)
    (hstop : ∀ w : σ, gtest (fpop w none) = false)
    (hval : ∀ (w : σ) (y : Γ ka), hpush (fpop w (some y)) = e y)
    (s : List (Γ ka)) :
    ∀ (v : σ) (S : ∀ k, List (Γ k)), S ka = s →
      (fun c : Option (Turing.TM2.Cfg Γ Λ σ) => c.bind (Turing.TM2.step M))^[s.length + 1]
          (some { l := some lc, var := v, stk := S })
        = some { l := some lnext,
                 var := fpop (s.foldl (fun w y => fpop w (some y)) v) none,
                 stk := Function.update (Function.update S ka []) kb
                          ((s.map e).reverse ++ S kb) } := by
  have hpeel : ∀ (n : ℕ) (c : Option (Turing.TM2.Cfg Γ Λ σ)),
      (fun c : Option (Turing.TM2.Cfg Γ Λ σ) => c.bind (Turing.TM2.step M))^[n + 1] c
        = (fun c : Option (Turing.TM2.Cfg Γ Λ σ) => c.bind (Turing.TM2.step M))^[n]
            ((fun c : Option (Turing.TM2.Cfg Γ Λ σ) => c.bind (Turing.TM2.step M)) c) := by
    intro n c
    first
      | (exact Function.iterate_succ_apply _ n c; done)
      | (rfl; done)
      | (rw [Function.iterate_succ_apply]; done)
      | (simp only [Function.iterate_succ_apply]; done)
  induction s with
  | nil =>
    intro v S hS
    have h1 := shiCopy_step_nil M hM hstop v S hS
    have hkb : (Function.update S ka ([] : List (Γ ka))) kb = S kb :=
      Function.update_of_ne (Ne.symm hab) _ _
    have hfix : Function.update (Function.update S ka ([] : List (Γ ka))) kb (S kb)
        = Function.update S ka ([] : List (Γ ka)) := by
      rw [← hkb]
      exact Function.update_eq_self kb _
    rw [hpeel, List.length_nil, Function.iterate_zero_apply]
    simp only [Option.bind_some, List.foldl_nil, List.map_nil, List.reverse_nil,
      List.nil_append]
    rw [h1, hfix]
  | cons x s' ih =>
    intro v S hS
    have h1 := shiCopy_step_cons M hab hM hcont hval x s' v S hS
    have hS' : (Function.update (Function.update S ka s') kb (e x :: S kb)) ka = s' := by
      rw [Function.update_of_ne hab, Function.update_self]
    have hS'kb : (Function.update (Function.update S ka s') kb (e x :: S kb)) kb
        = e x :: S kb := by
      rw [Function.update_self]
    have h2 := ih (fpop v (some x))
      (Function.update (Function.update S ka s') kb (e x :: S kb)) hS'
    rw [hS'kb] at h2
    have hother : ∀ k, k ≠ ka → k ≠ kb →
        (Function.update (Function.update S ka s') kb (e x :: S kb)) k = S k := by
      intro k ha' hb'
      rw [Function.update_of_ne hb', Function.update_of_ne ha']
    have hstk := shiCopy_update_two_eq ka kb
      (Function.update (Function.update S ka s') kb (e x :: S kb)) S hother
      ([] : List (Γ ka)) (((s'.map e).reverse ++ (e x :: S kb)))
    rw [List.length_cons, hpeel]
    simp only [Option.bind_some]
    rw [h1, h2]
    simp only [List.foldl_cons, List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append]
    rw [hstk]

/-- **The TM2 copy phase (one pass).**

Let `M` be a `TM2` machine whose statement at the designated label `lc` is the transfer loop

  `pop ka fpop (branch gtest (push kb hpush (goto fun _ => lc)) (goto fun _ => lnext))`,

where the internal state `σ` carries the element in transit: `fpop` loads the popped element
into the state, `gtest` reads off whether the pop succeeded (`hcont`, `hstop`), and `hpush`
reads the element back out, transported along the alphabet identification `e : Γ ka → Γ kb`
(`hval`).  Start from the configuration with label `lc`, internal state `v`, and stacks `S`,
where the source stack holds `S ka = s`.

Then after **exactly `s.length + 1` steps** the machine is at label `lnext` with the source
stack `ka` emptied and the target stack `kb` holding `(s.map e).reverse ++ S kb`; the internal
state is the corresponding left fold, and every other stack is untouched.

The first component is the raw iterate equation (the `evals_in_steps` field of
`StateTransition.EvalsTo`); the second repackages it as `StateTransition.EvalsToInTime` with
time bound `s.length + 1`, so that it can be chained with
`StateTransition.EvalsToInTime.trans` in an assembly proof.

Note the reversal: one pass reverses, so moving a stack while preserving its order takes two
passes through a scratch stack, i.e. `2 * s.length + 2` steps. -/
theorem solution {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type}
    (M : Λ → Turing.TM2.Stmt Γ Λ σ) {ka kb : K} (hab : ka ≠ kb) {lc lnext : Λ}
    {fpop : σ → Option (Γ ka) → σ} {gtest : σ → Bool} {hpush : σ → Γ kb} {e : Γ ka → Γ kb}
    (hM : M lc = Turing.TM2.Stmt.pop ka fpop
            (Turing.TM2.Stmt.branch gtest
              (Turing.TM2.Stmt.push kb hpush (Turing.TM2.Stmt.goto (fun _ => lc)))
              (Turing.TM2.Stmt.goto (fun _ => lnext))))
    (hcont : ∀ (w : σ) (y : Γ ka), gtest (fpop w (some y)) = true)
    (hstop : ∀ w : σ, gtest (fpop w none) = false)
    (hval : ∀ (w : σ) (y : Γ ka), hpush (fpop w (some y)) = e y)
    (s : List (Γ ka)) (v : σ) (S : ∀ k, List (Γ k)) (hS : S ka = s) :
    (fun c : Option (Turing.TM2.Cfg Γ Λ σ) => c.bind (Turing.TM2.step M))^[s.length + 1]
        (some { l := some lc, var := v, stk := S })
      = some { l := some lnext,
               var := fpop (s.foldl (fun w y => fpop w (some y)) v) none,
               stk := Function.update (Function.update S ka []) kb
                        ((s.map e).reverse ++ S kb) }
    ∧ Nonempty (StateTransition.EvalsToInTime (Turing.TM2.step M)
        { l := some lc, var := v, stk := S }
        (some { l := some lnext,
                var := fpop (s.foldl (fun w y => fpop w (some y)) v) none,
                stk := Function.update (Function.update S ka []) kb
                         ((s.map e).reverse ++ S kb) })
        (s.length + 1)) := by
  have hkey := shiCopy_iter M hab hM hcont hstop hval s v S hS
  refine ⟨hkey, ?_⟩
  first
    | (exact ⟨{ steps := s.length + 1, evals_in_steps := hkey, steps_le_m := le_rfl }⟩; done)
    | (exact ⟨⟨⟨s.length + 1, hkey⟩, le_rfl⟩⟩; done)
    | (refine ⟨{ steps := s.length + 1, evals_in_steps := ?_, steps_le_m := le_rfl }⟩; exact hkey; done)
    | (refine ⟨{ steps := s.length + 1, evals_in_steps := ?_, steps_le_m := le_rfl }⟩; simpa only [flip] using hkey; done)
