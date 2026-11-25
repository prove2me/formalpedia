-- Prove2me | solution 1 for ReciprocityTheory.Cheb.abs_rpow_neg_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:54:05.29216+00:00
-- url     : https://prove2.me/submissions/27b75968-0cbd-45d8-ab94-0e76ced8d967

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Theorems.Thm_ReciprocityTheory_Cheb_abs_exp_neg_mul_sub_le

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
theorem _root_.solution {s m N N' : ℝ} (hs : 1 ≤ s) (hm : 1 ≤ m) (hN : m ≤ N) (hN' : m ≤ N') :
    |N' ^ (-s) - N ^ (-s)| ≤ s * |Real.log N' - Real.log N| * m⁻¹ := by
  have hm0 : 0 < m := by linarith
  rw [Real.rpow_def_of_pos (by linarith), Real.rpow_def_of_pos (by linarith),
    mul_comm (Real.log N'), mul_comm (Real.log N)]
  have := abs_exp_neg_mul_sub_le hs (Real.log_nonneg hm) (Real.log_le_log hm0 hN')
    (Real.log_le_log hm0 hN)
  rwa [Real.exp_neg, Real.exp_log hm0] at this
end ReciprocityTheory.Cheb
