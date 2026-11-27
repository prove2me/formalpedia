-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_addBlockToSum_fst_bfab06e1e6b8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:54.346134+00:00
-- url     : https://prove2.me/submissions/42b6b47f-fea5-43e0-8fd8-9d3bac0f48c3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_StatementsGluing
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_LocallyFreeSpreadHyp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_AddBlockPullbackOfChartBundlePullback

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
open ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} {ι : K → Type} {κ : Type}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (q : Σ o, addBlockIdx ι κ o) :
    (addBlockIdxEquiv q).1 = addBlockToSum q.1 := by
  rcases q with ⟨_ | k, i⟩ <;> rfl
end GroundTheory.Heights₂.Heights
