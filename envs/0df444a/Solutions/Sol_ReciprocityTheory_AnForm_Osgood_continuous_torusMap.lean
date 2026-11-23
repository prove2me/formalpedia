-- Prove2me | solution 1 for ReciprocityTheory.AnForm.Osgood.continuous_torusMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:07:19.953847+00:00
-- url     : https://prove2.me/submissions/2da6a300-e431-4304-99b2-818d0404c87c

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
theorem _root_.solution {n : ℕ} (c : Fin n → ℂ) (r : ℝ) :
    Continuous (torusMap c (fun _ => r)) := by
  refine continuous_pi fun i => ?_
  simp only [torusMap]
  fun_prop
end ReciprocityTheory.AnForm.Osgood
