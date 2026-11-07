-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.coneSlopeSq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T09:53:15.008198+00:00
-- url     : https://prove2.me/submissions/56e7ecf4-2a2b-474e-8f4f-e47d407c765f

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
theorem _root_.solution {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) :
    0 ≤ coneSlopeSq c := by
  unfold coneSlopeSq
  apply div_nonneg
  · nlinarith
  · positivity
end QEC.Coding.ProbabilisticConstruction.SphericalCap
