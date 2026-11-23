-- Prove2me | solution 1 for ReciprocityTheory.AnForm.Osgood.mem_ball_pi_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:21:14.046802+00:00
-- url     : https://prove2.me/submissions/91a12b2d-c19f-42a1-a853-76539e147374

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
theorem _root_.solution {n : ℕ} {c z : Fin n → ℂ} {r : ℝ} (hr : 0 < r) :
    z ∈ ball c r ↔ ∀ i, z i ∈ ball (c i) r := by
  rw [ball_pi c hr, Set.mem_univ_pi]
end ReciprocityTheory.AnForm.Osgood
