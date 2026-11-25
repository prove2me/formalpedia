-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_Dn_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:27:38.44734+00:00
-- url     : https://prove2.me/submissions/6a76920f-65eb-4d76-9916-b5c00412877b

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
theorem _root_.solution (p r : ℕ) : (sbDn p r)ᴴ = sbDn p r := by
  simp only [sbDn, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp
end ReciprocityTheory.MultiplicativeHeights
