-- Prove2me | solution 1 for ReciprocityTheory.Cheb.pow_le_norm_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:44:40.909814+00:00
-- url     : https://prove2.me/submissions/7890a524-b4e9-4b89-b10b-698de93bb828

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {z : mixedSpace E} {b : ℝ} (hb : 0 ≤ b) (h : ∀ w, b ≤ normAtPlace w z) :
    b ^ Module.finrank ℚ E ≤ mixedEmbedding.norm z := by
  rw [mixedEmbedding.norm_apply, ← sum_mult_eq, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod (fun w _ => pow_nonneg hb _) (fun w _ => pow_le_pow_left₀ hb (h w) _)
end ReciprocityTheory.Cheb
