-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.le_tmax
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:33:18.090487+00:00
-- url     : https://prove2.me/submissions/b0105b09-d96c-46dc-915e-a9287bb5ab61

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_ContinuousTmaxShift
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


theorem solution (t : ι → ℝ) (i : ι) : t i ≤ tmax t := by
  exact Finset.le_sup' t (Finset.mem_univ i)
