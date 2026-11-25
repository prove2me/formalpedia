-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_addBlockPullback_of_chartBundlePullback_af7b4b77c248
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:48.743954+00:00
-- url     : https://prove2.me/submissions/3f2d552c-74a9-4a2c-8206-ca84a092cd38

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
variable {Ω Ω' : Type} [Field Ω] [Field Ω'] [Algebra Ω Ω'] {ι κ : Type}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (h : ChartBundlePullback.Statement) :
    IndefiniteRowSideFullHecke.Antisym.AddBlockPullback.Statement := by
  intro Ω Ω' _ _ _ _ ι κ _ _ x z r E _ _ B
  exact h Ω Ω' ι κ x z r E B
end GroundTheory.Heights₂.Heights
