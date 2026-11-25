-- Prove2me | solution 1 for ReciprocityTheory.Cheb.abs_log_sub_log_le_of_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:55.14705+00:00
-- url     : https://prove2.me/submissions/09c4fa85-3b06-49a1-847b-93b043d5d3f6

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
namespace ReciprocityTheory.Cheb
theorem _root_.solution {a b δ : ℝ} (hb : 0 < b) (hab : |a - b| ≤ δ) (ha : b / 2 ≤ a) :
    |Real.log a - Real.log b| ≤ 2 * δ / b := by
  have ha0 : 0 < a := by linarith
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hab
  rw [abs_le] at hab ⊢
  constructor
  · have h1 : Real.log (b / a) ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb ha0)
    rw [Real.log_div hb.ne' ha0.ne'] at h1
    have h2 : b / a - 1 ≤ 2 * δ / b := by
      rw [div_sub_one ha0.ne', div_le_div_iff₀ ha0 hb]
      nlinarith
    linarith
  · have h1 : Real.log (a / b) ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb)
    rw [Real.log_div ha0.ne' hb.ne'] at h1
    have h2 : a / b - 1 ≤ 2 * δ / b := by
      rw [div_sub_one hb.ne']
      apply div_le_div_of_nonneg_right _ hb.le
      linarith
    linarith
end ReciprocityTheory.Cheb
