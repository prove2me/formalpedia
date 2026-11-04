-- Prove2me | solution 1 for ThreeSum.WeightedModuli.joint_dvd_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:39:01.382111+00:00
-- url     : https://prove2.me/submissions/376a2f74-f18b-4b21-9be2-7a097fbc535d

import Definitions.Def_Submission_ThreeSum_Auxiliary
import Definitions.Def_Submission_ThreeSum_WeightedModuli
import Theorems.Thm_ThreeSum_Arithmetic_missWeight_zero
import Definitions.Def_WeightedCache3SUM_Alias_b1605bee33c94013
attribute [local simp] ThreeSum.Arithmetic.missWeight_zero



set_option autoImplicit false
open ThreeSum ThreeSum.WeightedModuli
open Finset Arithmetic
open scoped BigOperators
namespace ThreeSum.WeightedModuli
theorem _root_.solution (q p : ℕ) (hp : Nat.Prime p) (z : ℤ) :
    (joint q p : ℤ) ∣ z ↔ (q : ℤ) ∣ z ∧ (p : ℤ) ∣ z := by
  by_cases h : p ∣ q
  · simp only [joint, if_pos h]
    exact ⟨fun hz => ⟨hz, (Int.natCast_dvd_natCast.mpr h).trans hz⟩, fun hz => hz.1⟩
  · simp only [joint, if_neg h, Nat.cast_mul]
    have hc : IsCoprime (q : ℤ) (p : ℤ) :=
      ((hp.coprime_iff_not_dvd.mpr h).symm).isCoprime
    obtain ⟨u, v, huv⟩ := hc
    exact mul_dvd_iff_of_bezout ⟨u, v, huv⟩
end ThreeSum.WeightedModuli
