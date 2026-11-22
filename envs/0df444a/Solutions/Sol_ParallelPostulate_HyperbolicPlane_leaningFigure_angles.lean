-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.leaningFigure_angles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:19:27.180495+00:00
-- url     : https://prove2.me/submissions/5a4e84f8-859f-433c-9252-aadee96e726f

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution :
    leaningFigure.a.dir.1 * leaningFigure.b.dir.1
        + leaningFigure.a.dir.2 * leaningFigure.b.dir.2 = 0 ∧
      ((4 / 5 : ℚ)) ^ 2 = 1 + (-1) * (-3 / 5) ^ 2 ∧
      shift (-1 : ℚ) (-3 / 5) (4 / 5) leaningFigure.a.one = (0, 0) ∧
      shift (-1 : ℚ) (-3 / 5) (4 / 5) leaningFigure.a.zero = (-3 / 5, 0) ∧
      shift (-1 : ℚ) (-3 / 5) (4 / 5) leaningFigure.c.one = (-15 / 169, 100 / 169) ∧
      (0 : ℚ) < (-15 / 169) * (-3 / 5) + (100 / 169) * 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [leaningFigure, Dim.dir]
  · norm_num
  · apply Prod.ext <;> norm_num [leaningFigure, shift]
  · apply Prod.ext <;> norm_num [leaningFigure, shift]
  · apply Prod.ext <;> norm_num [leaningFigure, shift]
  · norm_num
end ParallelPostulate.HyperbolicPlane
