-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_Dp_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:20:24.712682+00:00
-- url     : https://prove2.me/submissions/55aaddc1-db5e-4f49-ac99-8bb8274aebf0

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
theorem _root_.solution (p r : ℕ) : (sbDp p r)ᴴ = sbDp p r := by
  simp only [sbDp, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp
end ReciprocityTheory.MultiplicativeHeights
