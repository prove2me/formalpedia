-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_A_abs_le_of_k__ne_3ed6a6aa9d98
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:45:15.855786+00:00
-- url     : https://prove2.me/submissions/74766563-08b6-4c8c-aaca-e8d6a48fef42

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
variable {ι : Type*} [Fintype ι]
namespace ReciprocityTheory.AnForm.A
theorem _root_.solution {x : ℝ} (h : kθ x ≠ 0) : |x| ≤ 1 / 2 := by
  have hx : x ∈ Function.support kθ := h
  unfold kθ at hx
  rw [ContDiffBump.support_normed_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  exact hx.le
end ReciprocityTheory.AnForm.A
