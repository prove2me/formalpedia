-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_Dp_mul_Dp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:48:55.475326+00:00
-- url     : https://prove2.me/submissions/17b7fd12-72bc-4eb0-81b8-417cdc9e22c0

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution (p r : ℕ) : sbDp p r * sbDp p r = sbDp p r := by
  simp only [sbDp, diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num
end ReciprocityTheory.MultiplicativeHeights
