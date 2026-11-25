-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_Dp_mul_Dn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:27:40.213544+00:00
-- url     : https://prove2.me/submissions/d03e4f88-d90a-46bb-afab-93dc1ef985f7

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
theorem _root_.solution (p r : ℕ) : sbDp p r * sbDn p r = 0 := by
  simp only [sbDp, sbDn, diagonal_mul_diagonal]
  rw [← diagonal_zero]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num
end ReciprocityTheory.MultiplicativeHeights
