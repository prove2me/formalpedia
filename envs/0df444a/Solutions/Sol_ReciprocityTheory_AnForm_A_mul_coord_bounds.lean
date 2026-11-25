-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.mul_coord_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:09:51.558022+00:00
-- url     : https://prove2.me/submissions/3e7a92eb-04fa-474a-842f-163f97cfcae3

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_abs_le_of_kK_ne

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
theorem _root_.solution {η : ℝ} (hη : 0 ≤ η) {h : ι → ℝ} (hh : kK h ≠ 0) (j : ι) :
    -(η / 2) ≤ η * h j ∧ η * h j ≤ η / 2 := by
  obtain ⟨h1, h2⟩ := abs_le.1 (abs_le_of_kK_ne hh j)
  constructor
  · nlinarith [mul_nonneg hη (by linarith : (0 : ℝ) ≤ h j + 1 / 2)]
  · nlinarith [mul_nonneg hη (by linarith : (0 : ℝ) ≤ 1 / 2 - h j)]
end ReciprocityTheory.AnForm.A
