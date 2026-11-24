-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.continuous_tmax_shift
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T01:40:22.230546+00:00
-- url     : https://prove2.me/submissions/4158cee1-a2ac-41dc-86a9-3dc473df0cf2

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


theorem solution (η : ℝ) (t : ι → ℝ) :
    Continuous (fun h : ι → ℝ => tmax (fun j => t j + η * h j)) := by
  classical
  let F : ι → (ι → ℝ) → ℝ := fun i h => t i + η * h i
  have h := Continuous.finset_sup' (f := F) Finset.univ_nonempty (fun i _ => continuous_const.add (continuous_const.mul (continuous_apply i)))
  have eq : (fun h : ι → ℝ => tmax (fun j => t j + η * h j)) = Finset.univ.sup' Finset.univ_nonempty F := by
    funext v
    exact (Finset.sup'_apply Finset.univ_nonempty F v).symm
  rw [eq]; exact h
