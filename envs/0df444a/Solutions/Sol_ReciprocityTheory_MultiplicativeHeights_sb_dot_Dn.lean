-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_dot_Dn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:40:12.428378+00:00
-- url     : https://prove2.me/submissions/e5450c3a-4efc-4621-b61c-823a665c08de

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_Dn_mul_Dn
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_sb_Dn_herm
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
    star v ⬝ᵥ (sbDn p r *ᵥ w) = star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  have h := sb_herm_swap (sb_Dn_herm p r) v (sbDn p r *ᵥ w)
  rw [mulVec_mulVec, sb_Dn_mul_Dn] at h
  exact h
end ReciprocityTheory.MultiplicativeHeights
