-- Prove2me | solution 1 for ReciprocityTheory.AnForm.Osgood.norm_torusMap_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:14.631844+00:00
-- url     : https://prove2.me/submissions/5e251d09-c4c3-4df1-8aeb-a76df5962567

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_OsgoodA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.Osgood
open Complex Metric MeasureTheory Set Filter Topology
open scoped Real
namespace ReciprocityTheory.AnForm.Osgood
theorem _root_.solution {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin n → ℝ) (i : Fin n) :
    ‖torusMap c (fun _ => r) θ i - c i‖ = r := by
  have h : torusMap c (fun _ => r) θ i - c i = (r : ℂ) * exp ((θ i : ℂ) * I) := by
    simp only [torusMap]
    ring
  have h1 : ‖exp ((θ i : ℂ) * I)‖ = 1 := by
    exact Complex.norm_exp_ofReal_mul_I _
  have h2 : ‖(r : ℂ)‖ = r := by
    exact Complex.norm_of_nonneg hr
  rw [h, norm_mul, h1, h2, mul_one]
end ReciprocityTheory.AnForm.Osgood
