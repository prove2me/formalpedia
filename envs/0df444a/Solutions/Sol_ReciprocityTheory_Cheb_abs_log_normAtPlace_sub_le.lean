-- Prove2me | solution 1 for ReciprocityTheory.Cheb.abs_log_normAtPlace_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:55:26.837096+00:00
-- url     : https://prove2.me/submissions/09f2b6e1-f71b-4020-8f93-1dcab1c58c0f

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
import Theorems.Thm_ReciprocityTheory_Cheb_abs_log_sub_log_le_of_half
import Theorems.Thm_ReciprocityTheory_Cheb_abs_normAtPlace_add_sub_le
import Theorems.Thm_ReciprocityTheory_Cheb_half_le_normAtPlace_add

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
    (hy : ∀ w, a ≤ normAtPlace w y) (w : InfinitePlace E) :
    |Real.log (normAtPlace w (y + k)) - Real.log (normAtPlace w y)| ≤ 2 * B / a := by
  have ha0 : 0 < a := by linarith
  have hw : 0 < normAtPlace w y := lt_of_lt_of_le ha0 (hy w)
  refine (abs_log_sub_log_le_of_half hw ((abs_normAtPlace_add_sub_le w y k).trans hk)
    (half_le_normAtPlace_add hk ha hy w)).trans ?_
  exact div_le_div_of_nonneg_left (by linarith) ha0 (hy w)
end ReciprocityTheory.Cheb
