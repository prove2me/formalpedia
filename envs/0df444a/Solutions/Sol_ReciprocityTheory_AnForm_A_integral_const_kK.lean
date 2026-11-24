-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integral_const_kK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:32.405417+00:00
-- url     : https://prove2.me/submissions/a532ed49-03c2-4e89-9f8b-743b689d16c2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
import Theorems.Thm_ReciprocityTheory_AnForm_A_kK_integral

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
theorem _root_.solution (c : ℝ) : ∫ h : ι → ℝ, c * kK h = c := by
  first
    | rw [integral_const_mul, kK_integral, mul_one]
    | rw [integral_mul_left, kK_integral, mul_one]
end ReciprocityTheory.AnForm.A
