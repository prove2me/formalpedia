-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.integral_kK_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:32.778621+00:00
-- url     : https://prove2.me/submissions/e529fb21-a444-4e2d-b488-bff396889901

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
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {F G : (ι → ℝ) → ℝ} (hFG : ∀ h, kK h ≠ 0 → F h = G h) :
    ∫ h, F h * kK h = ∫ h, G h * kK h := by
  congr 1
  funext h
  by_cases hh : kK h = 0
  · rw [hh, mul_zero, mul_zero]
  · rw [hFG h hh]
end ReciprocityTheory.AnForm.A
