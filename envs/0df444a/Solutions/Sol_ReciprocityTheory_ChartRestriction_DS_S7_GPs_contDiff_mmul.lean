-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.GPs.contDiff_mmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:15:56.483748+00:00
-- url     : https://prove2.me/submissions/07cff4d6-edd9-4112-9f32-b01f0ff7dc6f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_ContinuousOnFderivPhiP
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_GelfandPsB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiff_entry
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_S7_GPs_contDiff_mat
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
theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] {f g : X → Matrix (Fin n) (Fin n) ℂ}
    (hf : ContDiff ℂ ∞ f) (hg : ContDiff ℂ ∞ g) : ContDiff ℂ ∞ (fun x => f x * g x) := by
  apply contDiff_mat
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun k _ => ((contDiff_entry i k).comp hf).mul ((contDiff_entry k j).comp hg)
end ReciprocityTheory.ChartRestriction.DS.S7.GPs
