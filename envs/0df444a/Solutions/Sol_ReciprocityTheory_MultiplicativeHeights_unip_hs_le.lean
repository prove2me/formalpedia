-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.unip_hs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:26:09.218912+00:00
-- url     : https://prove2.me/submissions/e23851db-c61b-4f73-abde-95bac0e17b17

import Definitions.Def_ReciprocityTheory_SemistableReduction_LatSemiSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_UnipotentB
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
theorem _root_.solution {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (c : ℝ)
    (hA : ∀ u, normSq (A *ᵥ u) ≤ c * normSq u) :
    ∑ a, ∑ b, ‖A a b‖ ^ 2 ≤ r * c := by
  rw [Finset.sum_comm]
  calc ∑ b, ∑ a, ‖A a b‖ ^ 2 = ∑ b : Fin r, normSq (A *ᵥ Pi.single b 1) :=
        Finset.sum_congr rfl fun b _ => (unip_normSq_col A b).symm
    _ ≤ ∑ _b : Fin r, c := by
        refine Finset.sum_le_sum fun b _ => ?_
        have h := hA (Pi.single b 1)
        rwa [unip_normSq_single, mul_one] at h
    _ = r * c := by simp
end ReciprocityTheory.MultiplicativeHeights
