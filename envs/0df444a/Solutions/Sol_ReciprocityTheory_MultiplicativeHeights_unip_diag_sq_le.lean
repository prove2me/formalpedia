-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.unip_diag_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:34:21.193567+00:00
-- url     : https://prove2.me/submissions/8849b5af-418a-46f8-b653-624437d5cdaf

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentB
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_normSq_pow_le
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_normSq_col
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_unip_normSq_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) (n : ℕ) (i : Fin r) :
    ‖(A ^ n) i i‖ ^ 2 ≤ c ^ n := by
  have h1 := unip_normSq_pow_le A c hc hA n (Pi.single i 1)
  rw [unip_normSq_col, unip_normSq_single, mul_one] at h1
  refine le_trans ?_ h1
  exact Finset.single_le_sum (f := fun k => ‖(A ^ n) k i‖ ^ 2) (fun k _ => by positivity)
    (Finset.mem_univ i)
end ReciprocityTheory.MultiplicativeHeights
