-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.norm_coordMax_sub_le_half
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:19:06.8773+00:00
-- url     : https://prove2.me/submissions/e74037bf-892f-4054-9e37-c1f6bc0448a0

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tsupport_fderiv2_kK
import Theorems.Thm_ReciprocityTheory_AnForm_A_abs_tmax_sub_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open MeasureTheory Metric Filter Topology
open scoped ContDiff Interval
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution (s₀ s : ι → ℝ) (hs : fderiv ℝ (fderiv ℝ (kK : (ι → ℝ) → ℝ)) s ≠ 0) :
    ‖tmax (s₀ - s) - tmax s₀‖ ≤ 1 / 2 := by
  have hs' : ‖s‖ ≤ 1 / 2 :=
    mem_closedBall_zero_iff.1 (tsupport_fderiv2_kK (subset_tsupport _ hs))
  have := abs_tmax_sub_le (s₀ - s) s₀
  rw [sub_sub_cancel_left, norm_neg] at this
  rw [Real.norm_eq_abs]; exact this.trans hs'
end ReciprocityTheory.AnForm.A
