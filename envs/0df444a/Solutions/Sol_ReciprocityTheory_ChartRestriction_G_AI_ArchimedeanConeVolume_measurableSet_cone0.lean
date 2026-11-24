-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume.measurableSet_cone0
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:36:54.29319+00:00
-- url     : https://prove2.me/submissions/2c101a43-7df9-4474-95f8-7ac4e93b5de2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KappaA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LintegralIoiOfRealMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set Real
open scoped ENNReal Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
namespace ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
theorem _root_.solution {s : Set ℝ} (hs : MeasurableSet s) :
    MeasurableSet {y : E3 | 0 < ‖y‖ ∧ ‖y‖ < 1 ∧ y 0 / ‖y‖ ∈ s} := by
  refine (measurableSet_lt measurable_const measurable_norm).inter
    ((measurableSet_lt measurable_norm measurable_const).inter ?_)
  exact (by fun_prop : Measurable fun y : E3 => y 0 / ‖y‖) hs
end ReciprocityTheory.ChartRestriction.G.AI.ArchimedeanConeVolume
