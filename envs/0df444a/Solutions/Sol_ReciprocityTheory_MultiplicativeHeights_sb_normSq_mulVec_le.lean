-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sb_normSq_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:30:53.225482+00:00
-- url     : https://prove2.me/submissions/dbdd6e69-4012-4f1e-895a-a0e25d2a6126

import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_Unipotent
import Definitions.Def_ReciprocityTheory_SemistableReduction_ShareBallA

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
open Matrix NumberField
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (v : Fin r → ℂ) :
    normSq (A *ᵥ v) ≤ (∑ a, ∑ b, ‖A a b‖ ^ 2) * normSq v := by
  unfold normSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  calc ‖(A *ᵥ v) a‖ ^ 2 = ‖∑ b, A a b * v b‖ ^ 2 := rfl
    _ ≤ (∑ b, ‖A a b‖ * ‖v b‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) ((norm_sum_le _ _).trans (le_of_eq (by simp [norm_mul]))) 2
    _ ≤ (∑ b, ‖A a b‖ ^ 2) * (∑ b, ‖v b‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
end ReciprocityTheory.MultiplicativeHeights
