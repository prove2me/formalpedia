-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.leaningFigure_meets_beyond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:15:58.782919+00:00
-- url     : https://prove2.me/submissions/e9bd2e8c-6d7f-4cf4-abbd-a2b913bfbc9d

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
    leaningFigure.b.pt 10 = (0, 5) ∧ leaningFigure.c.pt 10 = (0, 5) ∧
      ((0 : ℚ), (5 : ℚ)) ∉ plane (-1 : ℚ) := by
  refine ⟨?_, ?_, ?_⟩
  · apply Prod.ext <;> norm_num [leaningFigure, Dim.pt]
  · apply Prod.ext <;> norm_num [leaningFigure, Dim.pt]
  · norm_num [plane]
end ParallelPostulate.HyperbolicPlane
