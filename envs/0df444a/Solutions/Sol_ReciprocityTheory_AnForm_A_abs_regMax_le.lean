-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.abs_regMax_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:40.406631+00:00
-- url     : https://prove2.me/submissions/5fee7123-93cb-4116-9573-7b3db2cec4be

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_zero
import Theorems.Thm_ReciprocityTheory_AnForm_A_abs_tmax_sub_le
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_ge
import Theorems.Thm_ReciprocityTheory_AnForm_A_regMax_le


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
theorem _root_.solution {η : ℝ} (hη : 0 ≤ η) (v : ι → ℝ) : |regMax η v| ≤ ‖v‖ + η / 2 := by
  have h1 := regMax_ge η v
  have h2 := regMax_le hη v
  have h3 := abs_tmax_sub_le v 0
  rw [tmax_zero, sub_zero, sub_zero] at h3
  rw [abs_le] at h3 ⊢; constructor <;> linarith
end ReciprocityTheory.AnForm.A
