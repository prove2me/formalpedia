-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_Dn_mul_Dn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:48:53.840826+00:00
-- url     : https://prove2.me/submissions/e3091851-4b06-4d3b-9224-1a1d00ba36d9

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
theorem _root_.solution (p r : ℕ) : sbDn p r * sbDn p r = sbDn p r := by
  simp only [sbDn, diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num
end ReciprocityTheory.MultiplicativeHeights
