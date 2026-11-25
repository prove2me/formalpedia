-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.abs_le_of_kK_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:58.337068+00:00
-- url     : https://prove2.me/submissions/ae8c89ba-b6e2-40c9-ae8e-6cee7142e051

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_norm_le_of_kK_ne

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
theorem _root_.solution {h : ι → ℝ} (hh : kK h ≠ 0) (j : ι) : |h j| ≤ 1 / 2 := by
  have e := norm_le_pi_norm h j
  rw [Real.norm_eq_abs] at e
  exact e.trans (norm_le_of_kK_ne hh)
end ReciprocityTheory.AnForm.A
