-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_measurable_tubeDens_109588edc399
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:48:01.594906+00:00
-- url     : https://prove2.me/submissions/2123e92f-b633-41b8-a5fb-0b56c61fc3ef

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCutOffTube
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeEuclMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffTube
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_measurable_tubeWeight_351f13760ff2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetSumMeasurable_measurable_sheetSum_0ce06e8414ea


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
open MvPolynomial MeasureTheory Filter Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) (P : MvPolynomial (Fin (d + 1)) ℂ)
    (R : ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (tubeDens J A P R φ) := by
  have hAm : Measurable fun x : Fin n → ℂ => A *ᵥ x :=
    (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).continuous.measurable
  have hw : Measurable ((Metric.closedBall (0 : Fin n → ℂ) R).indicator
      fun x => tubeWeight P (A *ᵥ x)) :=
    ((measurable_tubeWeight P).comp hAm).indicator measurableSet_closedBall
  exact SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
    (continuous_abs.comp continuous_mul).measurable hw _
end GroundTheory.Heights₂.Heights
