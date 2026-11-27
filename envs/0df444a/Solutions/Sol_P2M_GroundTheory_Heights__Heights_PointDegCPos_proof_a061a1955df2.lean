-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointDegCPos_proof_a061a1955df2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:07:39.259605+00:00
-- url     : https://prove2.me/submissions/92997fa2-834b-40f7-b8c3-098ef26f4ffa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_IsArithVarBotDualBlocksUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPointDegCPos
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointDegreeComplexPositive_card_algHom_pos_89873825872a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_full_25668629ca13


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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace PointDegCPos
theorem _root_.solution : PointDegCPos.Statement := by
  intro T _ K' _ _ y hP
  rw [IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.full Unit (fun _ => T) K' y hP]
  exact PointDegreeComplexPositive.card_algHom_pos _
end PointDegCPos
end GroundTheory.Heights₂.Heights
