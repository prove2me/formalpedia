-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.ii_of_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:51.228799+00:00
-- url     : https://prove2.me/submissions/a64d8ec6-c53d-4301-ba1b-7e39b31636b7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution {f : ℝ → ℝ} (hf : Measurable f) (B : ℝ) (hB : ∀ θ, |f θ| ≤ B) (a b : ℝ) :
    IntervalIntegrable f volume a b := by
  refine (intervalIntegrable_const (c := B)).mono_fun hf.aestronglyMeasurable ?_
  exact ae_of_all _ (fun θ => by
    simp only [Real.norm_eq_abs]
    exact (hB θ).trans (le_abs_self B))
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
