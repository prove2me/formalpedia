-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_dot_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:00:22.155437+00:00
-- url     : https://prove2.me/submissions/dd0d5e41-b906-4a60-ac8b-c61acbec4b5b

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_Dp_add_Dn
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_dot_Dp
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_dot_Dn

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
theorem _root_.solution (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ w = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) +
      star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  rw [← sb_dot_Dp p v w, ← sb_dot_Dn p v w, ← dotProduct_add, ← add_mulVec, sb_Dp_add_Dn,
    one_mulVec]
end ReciprocityTheory.MultiplicativeHeights
