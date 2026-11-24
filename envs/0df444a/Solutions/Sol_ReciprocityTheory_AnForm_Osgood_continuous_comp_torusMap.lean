-- Prove2me | solution 1 for ReciprocityTheory.AnForm.Osgood.continuous_comp_torusMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:52:37.905646+00:00
-- url     : https://prove2.me/submissions/fd2d07b5-f1df-4517-9a8f-904c65a26c0d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_OsgoodA
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_torusMap_mem_closedBall
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_continuous_torusMap

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
theorem _root_.solution {n : ℕ} {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hf : ∀ ζ ∈ closedBall c r, DifferentiableAt ℂ f ζ) :
    Continuous fun θ => f (torusMap c (fun _ => r) θ) := by
  refine continuous_iff_continuousAt.2 fun θ => ?_
  exact (hf _ (torusMap_mem_closedBall c hr θ)).continuousAt.comp
    (continuous_torusMap c r).continuousAt
end ReciprocityTheory.AnForm.Osgood
