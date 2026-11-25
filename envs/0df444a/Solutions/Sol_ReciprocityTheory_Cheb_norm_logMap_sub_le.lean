-- Prove2me | solution 1 for ReciprocityTheory.Cheb.norm_logMap_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:33:38.436468+00:00
-- url     : https://prove2.me/submissions/e79eb783-2a50-4932-83ae-8dbcc323e12f

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Theorems.Thm_ReciprocityTheory_Cheb_abs_logMap_sub_le

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
variable {y k : mixedSpace E} {B a : ℝ}
namespace ReciprocityTheory.Cheb
theorem _root_.solution (hB : 0 < B) (hk : ‖k‖ ≤ B) (ha : 2 * B ≤ a)
    (hy : ∀ w, a ≤ normAtPlace w y) : ‖logMap (y + k) - logMap y‖ ≤ 4 * (2 * B / a) := by
  have hδ : 0 ≤ 2 * B / a := div_nonneg (by linarith) (by linarith)
  refine (pi_norm_le_iff_of_nonneg (by linarith)).mpr fun w => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact abs_logMap_sub_le hB hk ha hy w
end ReciprocityTheory.Cheb
