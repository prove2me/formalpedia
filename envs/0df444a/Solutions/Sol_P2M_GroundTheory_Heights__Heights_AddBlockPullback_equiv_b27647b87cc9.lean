-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AddBlockPullback_equiv_b27647b87cc9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:52:23.738841+00:00
-- url     : https://prove2.me/submissions/ec0fd3aa-041d-4382-9d13-d52f5b1bab21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AlgebraMapMemChartRingJoinPt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartBundlePullback_holds_6b29b49f8013
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_addBlockPullback_of_chartBundlePullback_af7b4b77c248


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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo TensorProduct
namespace GroundTheory.Heights₂.Heights
namespace AddBlockPullback
theorem _root_.solution :
    ChartBundlePullback.Statement ↔ IndefiniteRowSideFullHecke.Antisym.AddBlockPullback.Statement :=
  ⟨addBlockPullback_of_chartBundlePullback, fun _ => chartBundlePullback_holds⟩
end AddBlockPullback
end GroundTheory.Heights₂.Heights
