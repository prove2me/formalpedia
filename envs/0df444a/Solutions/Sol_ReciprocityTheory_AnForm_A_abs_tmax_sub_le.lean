-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.abs_tmax_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:16.504972+00:00
-- url     : https://prove2.me/submissions/9665e32a-7b7d-429b-aab8-ee46ae8238cb

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_tmax_sub_le_norm

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
theorem _root_.solution (s t : ι → ℝ) : |tmax s - tmax t| ≤ ‖s - t‖ := by
  rw [abs_sub_le_iff]
  refine ⟨tmax_sub_le_norm s t, ?_⟩
  rw [norm_sub_rev]
  exact tmax_sub_le_norm t s
end ReciprocityTheory.AnForm.A
