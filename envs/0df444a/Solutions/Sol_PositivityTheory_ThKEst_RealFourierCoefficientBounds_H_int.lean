-- Prove2me | solution 1 for PositivityTheory.ThKEst.RealFourierCoefficientBounds.H_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:14:52.19852+00:00
-- url     : https://prove2.me/submissions/6ea285b6-d6cf-40b4-8b74-d8027b5c7bff

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefRealA
import Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_H_smooth
import Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_H_bound
import Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_wt_int

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
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
namespace PositivityTheory.ThKEst.RealFourierCoefficientBounds
theorem _root_.solution (N : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x : V) (j : ℕ), j ≤ N →
    Integrable (fun u => ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖) ∧
    (1 + ‖x‖) ^ N * ∫ u, ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤
      K * (q V (N + (Module.finrank ℝ V + 1)) N f₁ * q V (N + (Module.finrank ℝ V + 1)) N f₂) := by
  set D := Module.finrank ℝ V + 1 with hD
  refine ⟨2 ^ N * 2 ^ (N + D) * 2 ^ (N + D) * ∫ u : V, ((1 + ‖u‖) ^ D)⁻¹, ?_, fun f₁ f₂ x j hj => ?_⟩
  · have : 0 ≤ ∫ u : V, ((1 + ‖u‖) ^ D)⁻¹ := integral_nonneg fun u => by positivity
    positivity
  set C := 2 ^ N * ((2 ^ (N + D) * q V (N + D) N f₁) * (2 ^ (N + D) * q V (N + D) N f₂)) with hC
  have hb : ∀ u, (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ ≤ C * ((1 + ‖u‖) ^ D)⁻¹ := by
    intro u
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    have := H_bound N D f₁ f₂ x u hj
    linarith [mul_right_comm ((1 + ‖x‖) ^ N) ((1 + ‖u‖) ^ D) ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖]
  have hw : Integrable fun u : V => C * ((1 + ‖u‖) ^ D)⁻¹ := (wt_int (V := V)).const_mul C
  have hc : Continuous fun u => ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ :=
    ((H_smooth f₁ f₂ x).continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  have hi : Integrable fun u => ‖iteratedFDeriv ℝ j (H f₁ f₂ x) u‖ := by
    refine hw.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
    rw [norm_norm]
    refine le_trans ?_ (hb u)
    exact le_mul_of_one_le_left (norm_nonneg _) (one_le_pow₀ (by linarith [norm_nonneg x]))
  refine ⟨hi, ?_⟩
  rw [← integral_const_mul]
  refine (integral_mono (hi.const_mul _) hw hb).trans (le_of_eq ?_)
  rw [integral_const_mul, hC]; ring
end PositivityTheory.ThKEst.RealFourierCoefficientBounds
