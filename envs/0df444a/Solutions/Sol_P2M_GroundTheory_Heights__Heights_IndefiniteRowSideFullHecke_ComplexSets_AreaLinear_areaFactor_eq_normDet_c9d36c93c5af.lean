-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AreaLinear_areaFactor_eq_normDet_c9d36c93c5af
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:41.665793+00:00
-- url     : https://prove2.me/submissions/ffa480b0-bc52-45bf-974e-0ce23f88327c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotBotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FrameProjEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MeasureTheory Measure Metric Module
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AreaLinear
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AreaLinear
theorem _root_.solution {k m : ℕ}
    (L : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) :
    areaFactor L = L.normDet := by
  unfold areaFactor
  rw [← LinearMap.normDet_sq L]
  push_cast
  exact Real.sqrt_sq (LinearMap.normDet_nonneg L)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AreaLinear
