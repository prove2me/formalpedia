-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_coneBall_hausdorff_lt_top_a8bd40dcd9c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:25:48.254935+00:00
-- url     : https://prove2.me/submissions/e6b43271-e018-499f-b774-923a221b9881

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGram
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeChartArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeChartGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix Metric Set ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (hMF : MassFinite.Statement) {n e : ℕ} (h : HermNorm n)
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
      {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} < ⊤ := by
  have hdet : IsUnit (h.matᵀ).det := by rw [det_transpose]; exact h.isUnit_det
  let P : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 h.matᵀ)
  let Q : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Matrix.toLpLin 2 2 (h.matᵀ)⁻¹)
  have hsub : {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ q ∈ J, eval (h.pointOf z) q = 0} ⊆
      Q '' (zeroSetEuc J ∩ ball 0 (‖P‖ + 1)) := by
    rintro z ⟨hz, hzJ⟩
    refine ⟨P z, ⟨fun q hq => hzJ q hq, ?_⟩, ?_⟩
    · rw [mem_ball_zero_iff]
      calc ‖P z‖ ≤ ‖P‖ * ‖z‖ := P.le_opNorm z
        _ ≤ ‖P‖ * 1 := by gcongr
        _ < ‖P‖ + 1 := by linarith
    · ext i
      simp [P, Q, Matrix.toLpLin_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
  have hd : (0 : ℝ) ≤ ((2 * (e + 1) : ℕ) : ℝ) := by positivity
  calc _ ≤ Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (Q '' (zeroSetEuc J ∩ ball 0 (‖P‖ + 1))) :=
        measure_mono hsub
    _ ≤ (‖Q‖₊ : ENNReal) ^ ((2 * (e + 1) : ℕ) : ℝ) *
          Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (zeroSetEuc J ∩ ball 0 (‖P‖ + 1)) :=
        Q.lipschitz.hausdorffMeasure_image_le hd _
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hd ENNReal.coe_ne_top)
        (hMF n (e + 1) J hJ (by exact_mod_cast hdim) _)
end GroundTheory.Heights₂.Heights
