-- Prove2me | solution 1 for ThreeSum.PrimeChain.sum_scores_le_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:42:08.062199+00:00
-- url     : https://prove2.me/submissions/58eab911-3c1f-475b-8845-96584ff3f332

import Definitions.Def_Submission_ThreeSum_Arithmetic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Data.List.MinMax
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSum_PrimeChain
import Theorems.Thm_ThreeSum_PrimeChain_sum_scores
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.PrimeChain
open Finset
open scoped BigOperators
variable {ι : Type*}
namespace ThreeSum.PrimeChain
theorem _root_.solution (T : Finset ι) (difference : ι → ℤ) (weight : ℤ → ℕ)
    (hzero : weight 0 = 0) (C : Finset ℕ) (q K : ℕ)
    (hdivisors : ∀ i ∈ T, difference i ≠ 0 →
      (C.filter fun p => p ∣ (difference i).natAbs).card ≤ K) :
    (∑ p ∈ C, score T difference weight (q * p)) ≤ K * score T difference weight q := by
  rw [sum_scores, score, mul_sum]
  apply sum_le_sum
  intro i hi
  by_cases hz : difference i = 0
  · simp [hz, hzero]
  by_cases hq : q ∣ (difference i).natAbs
  · rw [if_pos hq]
    apply Nat.mul_le_mul_right
    apply le_trans (card_le_card ?_) (hdivisors i hi hz)
    intro p hp
    exact mem_filter.mpr ⟨(mem_filter.mp hp).1,
      dvd_trans (dvd_mul_left p q) (mem_filter.mp hp).2⟩
  · rw [if_neg hq, mul_zero]
    have hempty : (C.filter fun p => q * p ∣ (difference i).natAbs) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      exact hq (dvd_trans (dvd_mul_right q p) (mem_filter.mp hp).2)
    simp [hempty]
end ThreeSum.PrimeChain
