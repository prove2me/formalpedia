-- Prove2me | solution 1 for PositivityTheory.ThKEst.RealFourierCoefficientBounds.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:28:24.574433+00:00
-- url     : https://prove2.me/submissions/0847540d-6f31-4a04-bc5b-715d249a421d

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefRealA
import Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_q_cont
import Theorems.Thm_PositivityTheory_ThKEst_RealFourierCoefficientBounds_fourier_bound

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
theorem _root_.solution (N : ℕ) : ∃ p : Seminorm ℂ (SchwartzMap V ℂ), Continuous p ∧ ∀ (f₁ f₂ : SchwartzMap V ℂ) (x y : V),
    ‖∫ u, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ u y : ℝ)) * f₁ (u + x) * (starRingEnd ℂ) (f₂ u)‖ *
      (1 + ‖x‖ + ‖y‖) ^ N ≤ p f₁ * p f₂ := by
  obtain ⟨K, hK, h⟩ := fourier_bound (V := V) N
  let c : NNReal := ⟨Real.sqrt K, Real.sqrt_nonneg K⟩
  refine ⟨c • q V (N + (Module.finrank ℝ V + 1)) N, ?_, fun f₁ f₂ x y => ?_⟩
  · exact (q_cont _ _).const_smul c
  have e : (∫ u, Complex.exp (2 * Real.pi * Complex.I * (inner ℝ u y : ℝ)) * f₁ (u + x) *
      (starRingEnd ℂ) (f₂ u)) = 𝓕 (H f₁ f₂ x) (-y) := by
    rw [Real.fourier_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [H, inner_neg_right, smul_eq_mul, mul_assoc]
    congr 2
    push_cast; ring
  have h1 := h f₁ f₂ x (-y)
  rw [norm_neg] at h1
  rw [e]
  refine h1.trans (le_of_eq ?_)
  have hc : (c : ℝ) * c = K := Real.mul_self_sqrt hK
  simp only [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]
  rw [← hc]; ring
end PositivityTheory.ThKEst.RealFourierCoefficientBounds
