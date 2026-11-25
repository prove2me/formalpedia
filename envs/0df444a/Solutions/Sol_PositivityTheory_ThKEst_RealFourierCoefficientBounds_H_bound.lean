-- Prove2me | solution 1 for PositivityTheory.ThKEst.RealFourierCoefficientBounds.H_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:14.714845+00:00
-- url     : https://prove2.me/submissions/d91236ba-9db3-4ce8-9cf9-2eae527179f2

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefRealA
import Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_conj_smooth
import Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_shift_smooth
import Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_peetre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.RealFourierCoefficientBounds
open MeasureTheory SchwartzMap
open scoped FourierTransform ContDiff
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
namespace PositivityTheory.ThKEst.RealFourierCoefficientBounds
theorem _root_.solution (N D : ℕ) (f₁ f₂ : SchwartzMap V ℂ) (x u : V) {j : ℕ} (hj : j ≤ N) :
    (1 + ‖x‖) ^ N * (1 + ‖u‖) ^ D * ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤
      2 ^ N * ((2 ^ (N + D) * q V (N + D) N f₁) * (2 ^ (N + D) * q V (N + D) N f₂)) := by
  set A := 2 ^ (N + D) * q V (N + D) N f₁ with hA
  set B := 2 ^ (N + D) * q V (N + D) N f₂ with hB
  have hA0 : 0 ≤ A := by positivity
  have hB0 : 0 ≤ B := by positivity
  have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (shift_smooth f₁ x) (conj_smooth f₂) u (n := j)
    (by exact_mod_cast le_top)
  have key : ∀ i ∈ Finset.range (j + 1), (1 + ‖x‖) ^ N * (1 + ‖u‖) ^ D *
      ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun u => f₁ (u + x)) u‖ *
        ‖iteratedFDeriv ℝ (j - i) (fun u => (starRingEnd ℂ) (f₂ u)) u‖) ≤ (j.choose i : ℝ) * (A * B) := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have e1 : ‖iteratedFDeriv ℝ (j - i) (fun u => (starRingEnd ℂ) (f₂ u)) u‖ = ‖iteratedFDeriv ℝ (j - i) f₂ u‖ :=
      Complex.conjLIE.norm_iteratedFDeriv_comp_left f₂ u (j - i)
    rw [e1, iteratedFDeriv_comp_add_right (f := f₁)]
    have b1 : (1 + ‖u + x‖) ^ N * ‖iteratedFDeriv ℝ i f₁ (u + x)‖ ≤ A :=
      one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N + D, N)) (by simp) (by simp; omega) f₁ (u + x)
    have b2 : (1 + ‖u‖) ^ (N + D) * ‖iteratedFDeriv ℝ (j - i) f₂ u‖ ≤ B :=
      one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N + D, N)) (by simp) (by simp; omega) f₂ u
    have b3 : (1 + ‖x‖) ^ N ≤ (1 + ‖u + x‖) ^ N * (1 + ‖u‖) ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (peetre x u) N
    calc _ ≤ ((1 + ‖u + x‖) ^ N * (1 + ‖u‖) ^ N) * (1 + ‖u‖) ^ D *
          ((j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f₁ (u + x)‖ * ‖iteratedFDeriv ℝ (j - i) f₂ u‖) := by
          gcongr
      _ = (j.choose i : ℝ) * (((1 + ‖u + x‖) ^ N * ‖iteratedFDeriv ℝ i f₁ (u + x)‖) *
          ((1 + ‖u‖) ^ (N + D) * ‖iteratedFDeriv ℝ (j - i) f₂ u‖)) := by ring
      _ ≤ _ := by gcongr
  calc _ ≤ (1 + ‖x‖) ^ N * (1 + ‖u‖) ^ D * ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun u => f₁ (u + x)) u‖ *
        ‖iteratedFDeriv ℝ (j - i) (fun u => (starRingEnd ℂ) (f₂ u)) u‖ :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (A * B) := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum key
    _ = 2 ^ j * (A * B) := by
        rw [← Finset.sum_mul]; congr 1; exact_mod_cast Nat.sum_range_choose j
    _ ≤ 2 ^ N * (A * B) := by gcongr; norm_num
end PositivityTheory.ThKEst.RealFourierCoefficientBounds
