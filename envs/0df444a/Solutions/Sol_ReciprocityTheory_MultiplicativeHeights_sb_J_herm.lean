-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_J_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:27:41.478994+00:00
-- url     : https://prove2.me/submissions/8796af18-ab27-44b1-997d-9da0e24727ad

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
theorem _root_.solution (p r : ℕ) : (signMat p r)ᴴ = signMat p r := by
  simp only [signMat, sgn, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp
end ReciprocityTheory.MultiplicativeHeights
