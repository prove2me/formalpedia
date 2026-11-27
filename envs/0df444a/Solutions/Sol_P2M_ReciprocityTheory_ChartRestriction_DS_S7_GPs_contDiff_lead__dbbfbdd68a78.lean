-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiff_lead__dbbfbdd68a78
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:14:30.659828+00:00
-- url     : https://prove2.me/submissions/57bf4165-e6eb-47af-be7b-d49a786a917a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiff_entry
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
open Finset MeasureTheory Matrix
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
open ReciprocityTheory.ChartRestriction.DS.S7.GPs
namespace ReciprocityTheory.ChartRestriction.DS.S7.GPs
theorem _root_.solution (i : ℕ) : ContDiff ℂ ∞ (fun z : Matrix (Fin n) (Fin n) ℂ => lead i z) := by
  unfold lead
  by_cases h : i ≤ n
  · simp only [h, dite_true, Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
    refine ContDiff.sum fun σ _ => contDiff_const.mul ?_
    first
      | exact contDiff_prod fun l _ => contDiff_entry (Fin.castLE h (σ l)) (Fin.castLE h l)
      | exact ContDiff.finset_prod fun l _ => contDiff_entry (Fin.castLE h (σ l)) (Fin.castLE h l)
  · simp only [h, dite_false]
    exact contDiff_const
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
