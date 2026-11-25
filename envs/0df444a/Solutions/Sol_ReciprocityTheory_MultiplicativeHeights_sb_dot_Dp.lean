-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_dot_Dp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:37:57.9268+00:00
-- url     : https://prove2.me/submissions/60b20b62-4b7f-4d66-8255-ee9f6fcae6db

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_Dp_mul_Dp
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_Dp_herm
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_herm_swap

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
    star v ⬝ᵥ (sbDp p r *ᵥ w) = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) := by
  have h := sb_herm_swap (sb_Dp_herm p r) v (sbDp p r *ᵥ w)
  rw [mulVec_mulVec, sb_Dp_mul_Dp] at h
  exact h
end ReciprocityTheory.MultiplicativeHeights
