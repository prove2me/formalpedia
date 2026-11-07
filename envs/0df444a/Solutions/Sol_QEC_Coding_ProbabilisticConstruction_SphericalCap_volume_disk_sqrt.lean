-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.SphericalCap.volume_disk_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:37:04.532337+00:00
-- url     : https://prove2.me/submissions/a775cd43-9d0c-4906-bcbe-f5a45e272500

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
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) :
    volume (closedBall (0 : EuclideanSpace ℝ (Fin 2)) (Real.sqrt a)) =
      ENNReal.ofReal (Real.pi * a) := by
  rw [EuclideanSpace.volume_closedBall_fin_two, ← ENNReal.ofReal_pow,
    Real.sq_sqrt ha, ← ENNReal.ofReal_mul ha]
  · congr 1
    ring
  · positivity
end QEC.Coding.ProbabilisticConstruction.SphericalCap
