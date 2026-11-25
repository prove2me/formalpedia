-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_hausdorffMeasure_coneSet_ball_le_b81ecaae35f7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:48:10.834183+00:00
-- url     : https://prove2.me/submissions/b4f4b77f-b53a-4a74-8956-bbd21b17093a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeFiniteFibreDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeIntegralLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalMass
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_coneSet_iff_pointOfL_9f474107b28f

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
open MvPolynomial MeasureTheory
open scoped ENNReal NNReal
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (d : ℕ) (R : ℝ) :
    Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coneSet h J ∩ Metric.ball 0 R) ≤
      ((‖(h.pointOfL.symm : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖₊ : ℝ≥0∞) ^
          ((2 * d : ℕ) : ℝ)) *
        Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (zeroSetEuc J ∩
          Metric.ball 0 (‖(h.pointOfL : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R + 1)) := by
  set e := h.pointOfL
  have hsub : coneSet h J ∩ Metric.ball 0 R ⊆ e.symm '' (zeroSetEuc J ∩
      Metric.ball 0 (‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R + 1)) := by
    rintro y ⟨hy, hyR⟩
    refine ⟨e y, ⟨(mem_coneSet_iff_pointOfL h J y).1 hy, ?_⟩, e.symm_apply_apply y⟩
    rw [mem_ball_zero_iff] at hyR ⊢
    calc ‖e y‖ = ‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) y‖ := rfl
      _ ≤ ‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * ‖y‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R := by
        gcongr
      _ < _ := lt_add_one _
  calc _ ≤ Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (e.symm '' (zeroSetEuc J ∩
        Metric.ball 0 (‖(e : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n))‖ * R + 1))) :=
        measure_mono hsub
    _ ≤ _ := e.symm.lipschitz.hausdorffMeasure_image_le (by positivity) _
end GroundTheory.Heights₂.Heights
