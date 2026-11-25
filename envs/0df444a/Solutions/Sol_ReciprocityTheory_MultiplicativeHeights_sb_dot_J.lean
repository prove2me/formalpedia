-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_dot_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:56:09.960786+00:00
-- url     : https://prove2.me/submissions/0a35cd55-4a47-4ed1-9c04-c92a78b45433

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_signMat_eq
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
    star v ⬝ᵥ (signMat p r *ᵥ w) = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) -
      star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  rw [sb_signMat_eq, sub_mulVec, dotProduct_sub, sb_dot_Dp p v w, sb_dot_Dn p v w]
end ReciprocityTheory.MultiplicativeHeights
