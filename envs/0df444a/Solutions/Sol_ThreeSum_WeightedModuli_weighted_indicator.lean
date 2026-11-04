-- Prove2me | solution 1 for ThreeSum.WeightedModuli.weighted_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:43:54.016517+00:00
-- url     : https://prove2.me/submissions/f86e1be4-6aff-4d13-9149-676be63ce68d

import Definitions.Def_Submission_ThreeSum_Auxiliary
import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Theorems.Thm_ThreeSum_WeightedModuli_joint_dvd_iff
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_add_hits
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Theorems.Thm_ThreeSum_Auxiliary_moduli_card
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.WeightedModuli
open Finset Arithmetic
open scoped BigOperators
namespace ThreeSum.WeightedModuli
theorem _root_.solution (C : Finset ℕ) (hC : ∀ p ∈ C, Nat.Prime p)
    (q : ℕ) (z : ℤ) :
    (if (q : ℤ) ∣ z then missWeight (Auxiliary.moduli C) z else 0) +
      (∑ p ∈ C, dividesIndicator (joint q p) z) =
      C.card * dividesIndicator q z := by
  have hmod : (∑ p ∈ C, dividesIndicator (p : ℤ) z) =
      ∑ p ∈ Auxiliary.moduli C, dividesIndicator p z := by
    rw [Auxiliary.moduli, Finset.sum_image]
    intro a ha b hb heq
    exact Nat.cast_injective heq
  by_cases hq : (q : ℤ) ∣ z
  · have hjoint : (∑ p ∈ C, dividesIndicator (joint q p) z) =
        ∑ p ∈ C, dividesIndicator (p : ℤ) z := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [dividesIndicator, joint_dvd_iff q p (hC p hp), hq]
    rw [if_pos hq, hjoint, hmod]
    simpa [dividesIndicator, hq, Auxiliary.moduli_card] using
      missWeight_add_hits (Auxiliary.moduli C) z
  · have hjoint : (∑ p ∈ C, dividesIndicator (joint q p) z) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      simp [dividesIndicator, joint_dvd_iff q p (hC p hp), hq]
    rw [if_neg hq, hjoint]
    simp [dividesIndicator, hq]
end ThreeSum.WeightedModuli
