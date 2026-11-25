-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_J_mul_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:48:57.017166+00:00
-- url     : https://prove2.me/submissions/64af4cb6-f893-4518-9feb-47654df5c77c

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
theorem _root_.solution (p r : ℕ) : signMat p r * signMat p r = 1 := by
  simp only [signMat, sgn, diagonal_mul_diagonal]
  rw [← diagonal_one]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num
end ReciprocityTheory.MultiplicativeHeights
