-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.measurableSet_axialCone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:37:07.028501+00:00
-- url     : https://prove2.me/submissions/c140045b-7658-4a65-a182-4b3158ecbf62

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_AxialCoordinates
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_ConeSlices

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.SphericalCap
open MeasureTheory Metric Set
open scoped ENNReal
namespace QEC.Coding.ProbabilisticConstruction.SphericalCap
theorem _root_.solution (c : ℝ) : MeasurableSet (axialCone c) := by
  change MeasurableSet ({x : Ambient | ‖x‖ ≤ 1} ∩ {x | c * ‖x‖ ≤ x 0})
  exact (isClosed_le continuous_norm continuous_const).measurableSet.inter
    (isClosed_le (continuous_const.mul continuous_norm) (by fun_prop)).measurableSet
end QEC.Coding.ProbabilisticConstruction.SphericalCap
