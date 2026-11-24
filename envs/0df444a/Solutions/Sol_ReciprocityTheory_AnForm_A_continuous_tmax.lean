-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.continuous_tmax
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T01:40:12.137042+00:00
-- url     : https://prove2.me/submissions/abadfed7-a0dc-4237-b661-006bd4a2771b

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


theorem solution : Continuous (tmax : (ι → ℝ) → ℝ) := by
  classical
  let F : ι → (ι → ℝ) → ℝ := fun i t => t i
  have h := Continuous.finset_sup' (f := F) Finset.univ_nonempty (fun i _ => continuous_apply i)
  have eq : (tmax : (ι → ℝ) → ℝ) = Finset.univ.sup' Finset.univ_nonempty F := by
    funext v
    exact (Finset.sup'_apply Finset.univ_nonempty F v).symm
  rw [eq]; exact h
