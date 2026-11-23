-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshLap.continuous_circleMap_uncurry
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:43.572409+00:00
-- url     : https://prove2.me/submissions/4db5e754-6c35-4200-b8f7-f290ade9b666

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshLap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshLap
noncomputable section
namespace ReciprocityTheory.AnForm.A.PshLap
theorem _root_.solution : Continuous (fun p : ℝ × ℝ => circleMap 0 p.1 p.2) := by
  unfold circleMap; fun_prop
end ReciprocityTheory.AnForm.A.PshLap
