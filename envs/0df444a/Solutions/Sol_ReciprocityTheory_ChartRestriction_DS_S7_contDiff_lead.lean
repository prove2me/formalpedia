-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.contDiff_lead
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:59.370531+00:00
-- url     : https://prove2.me/submissions/1f66e032-0b24-4fe5-9989-90f6ca78fda4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_contDiff_entry

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (i : ℕ) {m : ℕ∞ω} : ContDiff ℂ m (lead (n := n) i) := by
  unfold lead
  by_cases h : i ≤ n
  · simp only [h, dif_pos]
    simp only [Matrix.det_apply, Units.smul_def]
    refine ContDiff.sum fun σ _ => ?_
    refine ContDiff.const_smul _ ?_
    refine contDiff_prod fun k _ => ?_
    simp only [Matrix.submatrix_apply]
    exact contDiff_entry _ _
  · simp only [h, dif_neg, not_false_eq_true]
    exact contDiff_const
end ReciprocityTheory.ChartRestriction.DS.S7
