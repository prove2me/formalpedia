-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AreaLinear_dividedDifference_real_holds_836c64b848bf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:57:15.684517+00:00
-- url     : https://prove2.me/submissions/97f54952-2356-4fe6-981e-560b248f271d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotBotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_FrameProjEq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_VolumeLtHausdorffUnitBallTwenty
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_AreaLinear_areaFactor_eq_normDet_c9d36c93c5af

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
theorem _root_.solution : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AreaLinear.Statement := by
  intro k m L _ A
  have h := LinearMap.hausdorffMeasure_image L A
  rw [finrank_euclideanSpace_fin] at h
  rw [h, areaFactor_eq_normDet]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.AreaLinear
