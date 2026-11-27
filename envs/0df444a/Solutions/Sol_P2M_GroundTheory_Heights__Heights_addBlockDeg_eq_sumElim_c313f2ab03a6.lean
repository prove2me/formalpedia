-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_addBlockDeg_eq_sumElim_c313f2ab03a6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:09:40.358202+00:00
-- url     : https://prove2.me/submissions/30c5cd35-8d3b-49ff-877e-4ba66213c09d

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
theorem _root_.solution (a : K → ℤ) :
    addBlockDeg a = Sum.elim a 0 ∘ addBlockToSum := by
  funext o
  rcases o with _ | k <;> rfl
end GroundTheory.Heights₂.Heights
