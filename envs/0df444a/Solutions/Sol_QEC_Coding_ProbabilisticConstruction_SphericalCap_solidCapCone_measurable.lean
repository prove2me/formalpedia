-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.solidCapCone_measurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:16.278639+00:00
-- url     : https://prove2.me/submissions/d1adeb41-5f4d-41c6-8fbc-df322f9aae2e

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_Measure
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeBridge

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal Pointwise
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (u : Sphere) (c : ℝ) :
    MeasurableSet (solidCapCone u c) := by
  change MeasurableSet ({x : Space | ‖x‖ ≤ 1} ∩
    {x | c * ‖x‖ ≤ inner ℝ (u : Space) x})
  exact (isClosed_le continuous_norm continuous_const).measurableSet.inter
    (isClosed_le (continuous_const.mul continuous_norm) (by fun_prop)).measurableSet
end QEC.Coding.ProbabilisticConstruction.SphericalCap
