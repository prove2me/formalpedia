-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagPairJoinLeft_proof_70799ddff699
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:05:58.341623+00:00
-- url     : https://prove2.me/submissions/1894a038-df56-471c-96cb-83c89f691e42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsBisSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinFlagPairJoinLeft
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_joinCoord_assocVar_b75e0e1aca5e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing div_mem_chartRing)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg joinCoord restrictChart chartMon IsGradedFrame IsUnitOn FlagPair IsPull
  IsVertDiv mcIdeal assocDeg assocVar joinCoord_assocVar)
open FlagPairJoinLeft
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace FlagPairJoinLeft
theorem _root_.solution (hVert : JoinVerticalDivisorLeft.Statement) : FlagPairJoinLeft.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w N V _ _ E E' EF E'F hF hF' φ EB E'B hB hB'
  exact ⟨assocFlagPair O x z w hF hF' hB hB' φ fun i => hVert O Ω K ι x K' ι' z K₂ ι₂ w _ _ _ (φ.vert i),
    rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
end FlagPairJoinLeft
end GroundTheory.Heights₂.Heights.NumbersDVR
