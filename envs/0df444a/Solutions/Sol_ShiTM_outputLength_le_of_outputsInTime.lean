-- Prove2me | solution 1 for ShiTM.outputLength_le_of_outputsInTime
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-14T18:51:43.863983+00:00
-- url     : https://prove2.me/submissions/cb271df5-f837-4b14-89e1-2b1651b10c41

import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Option.Basic
import Theorems.Thm_ShiTM_initList_haltList_laws

set_option autoImplicit false
set_option maxHeartbeats 1000000

-- `Turing.FinTM2` is a plain `structure`, not a `class`, so its instance-implicit fields are
-- *not* registered as instances (which is exactly why Mathlib has to declare
-- `Turing.FinTM2.decidableEqK` by hand, `Computability/TuringMachine/Computable.lean:80`).
-- Nothing supplies `Fintype tm.K`, so a sum `∑ k, _` over the stack index type of a bundled
-- machine does not even elaborate.  Register the field locally.
attribute [local instance] Turing.FinTM2.kFin

/-!
# A `TM2` machine's output is no longer than its input plus a constant times its running time

Given the per-step stack-growth bound `hc` (one `Turing.TM2.step` increases the total size of all
stacks by at most a constant `c`, uniformly in label, internal state and stack contents), a run of
`m` steps starting from the initial configuration on input `s` can only reach configurations of
total stack size at most `s.length + c * m`.  Since the halting configuration on output `t` has
total stack size `t.length`, this bounds the output length.

This is the fact that makes the time-bound arithmetic for a composition of polynomial-time `TM2`s
non-vacuous: the composed machine's running time depends on the length of the intermediate string
`|f a|`, and a polynomial bound for it exists only because `|f a|` is itself polynomially bounded.

Proof route.  `Turing.TM2OutputsInTime tm s (some t) m` unfolds to
`StateTransition.EvalsToInTime tm.step (initList tm s) (some (haltList tm t)) m`
(`Computability/TuringMachine/Computable.lean:135-137`), a structure with fields
`steps : ℕ`, `evals_in_steps : (flip bind f)^[steps] ↑a = b` (inherited from
`StateTransition.EvalsTo`, `Computability/StateTransition.lean:255-258`) and
`steps_le_m : steps ≤ m` (`Computability/StateTransition.lean:265-267`).  We induct on the iterate
count, collapse the total stack size of `initList`/`haltList` using the configuration laws, and
finish with `steps ≤ m`.
-/

/-- `flip bind f` is the one-step map on `Option σ`; on `some a` it is just `f a`. -/
private theorem shiOut_flip_bind_some {σ : Type} (f : σ → Option σ) (a : σ) :
    (flip bind f) (Option.some a) = f a := by
  first
  | (rfl
     done)
  | (simp only [flip, Option.bind_some]
     done)
  | (simp [flip]
     done)

/-- A halted (`none`) state is dead: `flip bind f` fixes it. -/
private theorem shiOut_flip_bind_none {σ : Type} (f : σ → Option σ) :
    (flip bind f) (Option.none : Option σ) = Option.none := by
  first
  | (rfl
     done)
  | (simp only [flip, Option.bind_none]
     done)
  | (simp [flip]
     done)

/-- Hence every iterate fixes it.  This is what rules out the halted case mid-run. -/
private theorem shiOut_iterate_none {σ : Type} (f : σ → Option σ) (n : ℕ) :
    (flip bind f)^[n] (Option.none : Option σ) = Option.none := by
  induction n with
  | zero =>
    first
    | (rfl
       done)
    | (rw [Function.iterate_zero_apply]
       done)
  | succ n ih =>
    first
    | (rw [Function.iterate_succ_apply, shiOut_flip_bind_none]
       exact ih
       done)
    | (simp only [Function.iterate_succ_apply, shiOut_flip_bind_none]
       exact ih
       done)

/-- **One step grows the total stack size by at most `c`.**

This is `hc` transported through `Turing.TM2.step`: the halted case `step ⟨none, _, _⟩ = none`
cannot produce a successor, and the running case `step ⟨some l, v, S⟩ = some (stepAux (m l) v S)`
is literally `hc`. -/
private theorem shiOut_step_bound (tm : Turing.FinTM2) (c : ℕ)
    (hc : ∀ (l : tm.Λ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
      ∑ k, ((Turing.TM2.stepAux (tm.m l) v S).stk k).length ≤ (∑ k, (S k).length) + c)
    (a b : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ) (h : tm.step a = Option.some b) :
    (∑ k, (b.stk k).length) ≤ (∑ k, (a.stk k).length) + c := by
  obtain ⟨l, v, S⟩ := a
  cases l with
  | none =>
    have h2 : (Option.none : Option (Turing.TM2.Cfg tm.Γ tm.Λ tm.σ)) = Option.some b := h
    first
    | (exact Option.noConfusion h2
       done)
    | (exact absurd h2 (by simp)
       done)
    | (simp at h2
       done)
  | some l =>
    have h2 : Option.some (Turing.TM2.stepAux (tm.m l) v S) = Option.some b := h
    have hb : Turing.TM2.stepAux (tm.m l) v S = b := by
      first
      | (exact Option.some.inj h2
         done)
      | (exact Option.some_injective _ h2
         done)
      | (injection h2 with h3
         exact h3
         done)
      | (simpa using h2
         done)
    rw [← hb]
    first
    | (exact hc l v S
       done)
    | (simpa using hc l v S
       done)

/-- **The iterated bound.**  If `n` applications of the one-step map carry `some a` to `some b`,
then the total stack size grew by at most `c * n`.  Induction on `n`; the halted branch is
impossible by `shiOut_iterate_none`. -/
private theorem shiOut_iter_bound (tm : Turing.FinTM2) (c : ℕ)
    (hc : ∀ (l : tm.Λ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
      ∑ k, ((Turing.TM2.stepAux (tm.m l) v S).stk k).length ≤ (∑ k, (S k).length) + c) :
    ∀ (n : ℕ) (a b : Turing.TM2.Cfg tm.Γ tm.Λ tm.σ),
      (flip bind tm.step)^[n] (Option.some a) = Option.some b →
        (∑ k, (b.stk k).length) ≤ (∑ k, (a.stk k).length) + c * n := by
  intro n
  induction n with
  | zero =>
    intro a b h
    have h1 : Option.some a = Option.some b := by
      first
      | (rw [← Function.iterate_zero_apply (flip bind tm.step) (Option.some a)]
         exact h
         done)
      | (exact h
         done)
    have h2 : a = b := by
      first
      | (exact Option.some.inj h1
         done)
      | (exact Option.some_injective _ h1
         done)
      | (injection h1 with h3
         exact h3
         done)
    subst h2
    first
    | (simp
       done)
    | (omega
       done)
  | succ n ih =>
    intro a b h
    have h' : (flip bind tm.step)^[n] (tm.step a) = Option.some b := by
      have hcopy := h
      first
      | (rw [Function.iterate_succ_apply, shiOut_flip_bind_some] at hcopy
         exact hcopy
         done)
      | (rw [Function.iterate_succ_apply] at hcopy
         exact hcopy
         done)
      | (simp only [Function.iterate_succ_apply, shiOut_flip_bind_some] at hcopy
         exact hcopy
         done)
      | (simp only [Function.iterate_succ_apply] at hcopy
         exact hcopy
         done)
    cases hsa : tm.step a with
    | none =>
      rw [hsa, shiOut_iterate_none] at h'
      first
      | (exact Option.noConfusion h'
         done)
      | (exact absurd h' (by simp)
         done)
      | (simp at h'
         done)
    | some a' =>
      rw [hsa] at h'
      have h1 := ih a' b h'
      have h2 := shiOut_step_bound tm c hc a a' hsa
      have h3 : c * (n + 1) = c * n + c := Nat.mul_succ c n
      first
      | (omega
         done)
      | (rw [h3]
         refine le_trans h1 ?_
         have h4 : (∑ k, (a.stk k).length) + (c * n + c)
             = ((∑ k, (a.stk k).length) + c) + c * n := by
           first
           | (ring
              done)
           | (omega
              done)
         rw [h4]
         exact Nat.add_le_add_right h2 (c * n)
         done)

/-- Total stack size of the initial configuration is the input length: the input stack holds `s`
and every other stack is empty, so the sum over `tm.K` collapses.  Uses the accepted platform
theorem `ShiTM.initList_haltList_laws` for the configuration laws. -/
private theorem shiOut_sum_initList (tm : Turing.FinTM2) (s : List (tm.Γ tm.k₀)) :
    ∑ k, ((Turing.initList tm s).stk k).length = s.length := by
  obtain ⟨-, -, hself, hne, -, -, -, -⟩ :=
    ShiTM.initList_haltList_laws tm s ([] : List (tm.Γ tm.k₁))
  have h0 : ∑ k ∈ Finset.univ.erase tm.k₀, ((Turing.initList tm s).stk k).length = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    rw [hne k (Finset.ne_of_mem_erase hk), List.length_nil]
  have hsplit : (∑ k ∈ Finset.univ.erase tm.k₀, ((Turing.initList tm s).stk k).length)
      + ((Turing.initList tm s).stk tm.k₀).length
      = ∑ k, ((Turing.initList tm s).stk k).length :=
    Finset.sum_erase_add Finset.univ
      (fun k => ((Turing.initList tm s).stk k).length) (Finset.mem_univ tm.k₀)
  rw [← hsplit, h0, hself, Nat.zero_add]

/-- Total stack size of the halting configuration is the output length. -/
private theorem shiOut_sum_haltList (tm : Turing.FinTM2) (t : List (tm.Γ tm.k₁)) :
    ∑ k, ((Turing.haltList tm t).stk k).length = t.length := by
  obtain ⟨-, -, -, -, -, -, hself, hne⟩ :=
    ShiTM.initList_haltList_laws tm ([] : List (tm.Γ tm.k₀)) t
  have h0 : ∑ k ∈ Finset.univ.erase tm.k₁, ((Turing.haltList tm t).stk k).length = 0 := by
    refine Finset.sum_eq_zero ?_
    intro k hk
    rw [hne k (Finset.ne_of_mem_erase hk), List.length_nil]
  have hsplit : (∑ k ∈ Finset.univ.erase tm.k₁, ((Turing.haltList tm t).stk k).length)
      + ((Turing.haltList tm t).stk tm.k₁).length
      = ∑ k, ((Turing.haltList tm t).stk k).length :=
    Finset.sum_erase_add Finset.univ
      (fun k => ((Turing.haltList tm t).stk k).length) (Finset.mem_univ tm.k₁)
  rw [← hsplit, h0, hself, Nat.zero_add]

/--
**A `TM2` machine's output is no longer than its input plus a constant times its running time.**

Let `tm` be a bundled `TM2` machine whose total stack size grows by at most `c` per
`Turing.TM2.step`, uniformly in the label, the internal state and the stack contents (hypothesis
`hc`; this is exactly the conclusion of `ShiTM.exists_stepAux_stack_growth_bound`).  If `tm`, run
on input `s`, outputs `t` within `m` steps, then `t.length ≤ s.length + c * m`.

The total stack size starts at `s.length` (the input stack holds `s`, all other stacks are empty),
increases by at most `c` on each of the at most `m` executed steps, and ends at `t.length` (the
output stack holds `t`, all other stacks are empty).

This is the missing link in the time-bound arithmetic for composing polynomial-time `TM2`s
(Mathlib's `proof_wanted Turing.TM2ComputableInPolyTime.comp`): the composed machine's running
time depends on the length of the intermediate string, and this theorem is what makes that length
-- hence the composite time bound -- polynomially bounded in the length of the original input.
-/
theorem solution {tm : Turing.FinTM2} (c : ℕ)
    (hc : ∀ (l : tm.Λ) (v : tm.σ) (S : ∀ k, List (tm.Γ k)),
      ∑ k, ((Turing.TM2.stepAux (tm.m l) v S).stk k).length ≤ (∑ k, (S k).length) + c)
    (s : List (tm.Γ tm.k₀)) (t : List (tm.Γ tm.k₁)) (m : ℕ)
    (h : Turing.TM2OutputsInTime tm s (Option.some t) m) :
    t.length ≤ s.length + c * m := by
  have h' : StateTransition.EvalsToInTime tm.step (Turing.initList tm s)
      (Option.some (Turing.haltList tm t)) m := h
  have hev : (flip bind tm.step)^[h'.steps] (Option.some (Turing.initList tm s))
      = Option.some (Turing.haltList tm t) := h'.evals_in_steps
  have hb := shiOut_iter_bound tm c hc h'.steps
    (Turing.initList tm s) (Turing.haltList tm t) hev
  rw [shiOut_sum_initList tm s, shiOut_sum_haltList tm t] at hb
  refine le_trans hb ?_
  first
  | (exact Nat.add_le_add_left (Nat.mul_le_mul_left c h'.steps_le_m) s.length
     done)
  | (exact Nat.add_le_add_left (Nat.mul_le_mul_left c h'.steps_le_m) _
     done)
  | (exact add_le_add_left (Nat.mul_le_mul_left c h'.steps_le_m) _
     done)
  | (have hm := Nat.mul_le_mul_left c h'.steps_le_m
     omega
     done)
