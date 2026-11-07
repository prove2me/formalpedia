-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.ball_le_coneSlopeSq_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:36:59.25845+00:00
-- url     : https://prove2.me/submissions/3ec18667-7791-4c0d-8fc6-64ed469fe449

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
theorem _root_.solution {c z : ℝ} (hc0 : 0 < c) (hcz : c ≤ z) :
    1 - z ^ 2 ≤ coneSlopeSq c * z ^ 2 := by
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc0
  rw [coneSlopeSq, div_mul_eq_mul_div, le_div_iff₀ hc2]
  nlinarith
end QEC.Coding.ProbabilisticConstruction.SphericalCap
