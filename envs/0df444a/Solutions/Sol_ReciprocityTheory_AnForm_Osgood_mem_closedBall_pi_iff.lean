-- Prove2me | solution 1 for ReciprocityTheory.AnForm.Osgood.mem_closedBall_pi_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:14.068902+00:00
-- url     : https://prove2.me/submissions/d3efdb33-84cd-4f6d-a7f1-e3aca5478bb6

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
theorem _root_.solution {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r) :
    z ∈ closedBall c r ↔ ∀ i, z i ∈ closedBall (c i) r := by
  rw [closedBall_pi c hr, Set.mem_univ_pi]
end ReciprocityTheory.AnForm.Osgood
