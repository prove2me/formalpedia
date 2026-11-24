-- Prove2me | solution 1 for ReciprocityTheory.AnForm.Osgood.torusMap_mem_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:45:41.348321+00:00
-- url     : https://prove2.me/submissions/828d9375-da3f-4da5-8af8-0482adb5c57e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_OsgoodA
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_mem_closedBall_pi_iff
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
theorem _root_.solution {n : ℕ} (c : Fin n → ℂ) {r : ℝ} (hr : 0 ≤ r) (θ : Fin n → ℝ) :
    torusMap c (fun _ => r) θ ∈ closedBall c r := by
  refine (mem_closedBall_pi_iff hr).2 fun i => ?_
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_torusMap_sub c hr θ i).le
end ReciprocityTheory.AnForm.Osgood
