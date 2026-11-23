-- Prove2me | solution 1 for ReciprocityTheory.AnForm.Osgood.torusMap_sub_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:04.124657+00:00
-- url     : https://prove2.me/submissions/8d3ad1a5-43a8-478d-b4d3-bf05b2c59b6e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_OsgoodA
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_mem_ball_pi_iff
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_norm_torusMap_sub

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
theorem _root_.solution {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) (hz : z ∈ ball c r)
    (θ : Fin n → ℝ) (i : Fin n) : torusMap c (fun _ => r) θ i - z i ≠ 0 := by
  intro h
  have h1 := (mem_ball_pi_iff hr).1 hz i
  rw [mem_ball, dist_eq_norm] at h1
  have h2 := norm_torusMap_sub c hr.le θ i
  rw [sub_eq_zero] at h
  rw [h] at h2
  linarith
end ReciprocityTheory.AnForm.Osgood
