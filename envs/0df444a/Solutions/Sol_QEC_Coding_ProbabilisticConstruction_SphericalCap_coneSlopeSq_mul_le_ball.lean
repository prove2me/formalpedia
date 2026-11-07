-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.coneSlopeSq_mul_le_ball
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:36:58.21543+00:00
-- url     : https://prove2.me/submissions/5d82fde7-31e0-4b19-9977-d1223bb80658

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
theorem _root_.solution {c z : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    (hz0 : 0 ≤ z) (hzc : z ≤ c) :
    coneSlopeSq c * z ^ 2 ≤ 1 - z ^ 2 := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc0
  rw [coneSlopeSq, div_mul_eq_mul_div, div_le_iff₀ hc2]
  nlinarith
end QEC.Coding.ProbabilisticConstruction.SphericalCap
