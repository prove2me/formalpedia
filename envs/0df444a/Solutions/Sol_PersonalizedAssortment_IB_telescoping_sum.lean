-- Prove2me | solution 1 for PersonalizedAssortment.IB.telescoping_sum
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:31:38.573262+00:00
-- url     : https://prove2.me/submissions/f9bfe4f5-e9c6-45ea-af71-0b8f56a155cf

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

set_option autoImplicit false
open scoped BigOperators

theorem solution (Ψ : ℝ → ℝ) (c : ℕ) (T : ℕ) (I : ℕ → ℕ) (hI0 : I 0 = c)
    (hstep : ∀ t < T, I (t + 1) ≤ I t ∧ I t ≤ I (t + 1) + 1) :
    ∑ t ∈ Finset.range T, Ψ ((I t : ℝ) / (c : ℝ)) * ((I t : ℝ) - (I (t + 1) : ℝ)) =
      ∑ k ∈ Finset.Ioc (I T) c, Ψ ((k : ℝ) / (c : ℝ)) := by
  induction T with
  | zero => simp [hI0]
  | succ T ih =>
    have hp : ∀ t < T, I (t + 1) ≤ I t ∧ I t ≤ I (t + 1) + 1 :=
      fun t ht => hstep t (Nat.lt_succ_of_lt ht)
    have hbound : ∀ t ≤ T + 1, I t ≤ c := by
      intro t
      induction t with
      | zero => intro _; exact hI0.le
      | succ t hi =>
        intro ht
        exact (hstep t (by omega)).1.trans (hi (by omega))
    have hs := hstep T (Nat.lt_succ_self T)
    rw [Finset.sum_range_succ, ih hp]
    by_cases heq : I T = I (T + 1)
    · simp [heq]
    · have hdrop : I T = I (T + 1) + 1 := by omega
      have hset : Finset.Ioc (I (T + 1)) c =
          insert (I (T + 1) + 1) (Finset.Ioc (I (T + 1) + 1) c) := by
        ext k
        simp only [Finset.mem_Ioc, Finset.mem_insert]
        have hb := hbound T (by omega)
        omega
      have hnot : I (T + 1) + 1 ∉ Finset.Ioc (I (T + 1) + 1) c := by simp
      rw [hdrop, hset, Finset.sum_insert hnot]
      push_cast
      ring

#print axioms solution
