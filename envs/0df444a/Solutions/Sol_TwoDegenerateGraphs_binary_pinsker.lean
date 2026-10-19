-- Prove2me | solution 1 for TwoDegenerateGraphs.binary_pinsker
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:04.05007+00:00
-- url     : https://prove2.me/submissions/7fffa6ce-b717-461a-9339-530cc3363828

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binaryPinskerGap_hasDerivAt
import Theorems.Thm_TwoDegenerateGraphs_binaryPinskerGap_convex

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution (q : ℝ) (hqzero : 0 ≤ q) (hqone : q ≤ 1) :
    Real.binEntropy q ≤
      Real.log 2 - (2 * q - 1) ^ 2 / 2 := by
  have habove :
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (2 : ℝ)⁻¹ ≤ x →
        0 ≤ binaryPinskerGap x := by
    intro x hxzero hxone hxhalf
    by_cases hxeq : x = (2 : ℝ)⁻¹
    · simp [hxeq]
    · have hxstrict : (2 : ℝ)⁻¹ < x :=
        lt_of_le_of_ne hxhalf (Ne.symm hxeq)
      have hmid :
          HasDerivAt binaryPinskerGap 0 ((2 : ℝ)⁻¹) := by
        convert binaryPinskerGap_hasDerivAt
          (q := (2 : ℝ)⁻¹) (by norm_num) (by norm_num) using 1
        exact binaryPinskerGapDeriv_half.symm
      have hslope := binaryPinskerGap_convex.le_slope_of_hasDerivAt
        (show (2 : ℝ)⁻¹ ∈ Set.Icc 0 1 by constructor <;> norm_num)
        (show x ∈ Set.Icc 0 1 from ⟨hxzero, hxone⟩)
        hxstrict hmid
      rw [slope_def_field, binaryPinskerGap_half, sub_zero] at hslope
      rcases (div_nonneg_iff.mp hslope) with hpositive | hnegative
      · exact hpositive.1
      · exfalso
        have hden : 0 < x - (2 : ℝ)⁻¹ := sub_pos.mpr hxstrict
        linarith [hnegative.2]
  by_cases hhalf : (2 : ℝ)⁻¹ ≤ q
  · have hgap := habove q hqzero hqone hhalf
    unfold binaryPinskerGap at hgap
    linarith
  · have hcomplement : (2 : ℝ)⁻¹ ≤ 1 - q := by
      norm_num at hhalf ⊢
      linarith
    have hgap := habove (1 - q) (sub_nonneg.mpr hqone)
      (by linarith) hcomplement
    unfold binaryPinskerGap at hgap
    rw [Real.binEntropy_one_sub] at hgap
    nlinarith
end TwoDegenerateGraphs
