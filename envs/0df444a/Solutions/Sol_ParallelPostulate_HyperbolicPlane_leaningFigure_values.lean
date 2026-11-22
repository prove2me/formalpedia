-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.leaningFigure_values
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:15:54.064863+00:00
-- url     : https://prove2.me/submissions/7ae38953-bfbf-4316-a780-cab3f1c58960

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
    leaningFigure.a.side leaningFigure.b.one = 3 / 10 ∧
      leaningFigure.a.side leaningFigure.c.one = 3 / 10 ∧
      cross leaningFigure.b.dir leaningFigure.c.dir = 3 / 100 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [leaningFigure, Dim.side, Dim.dir, cross]
end ParallelPostulate.HyperbolicPlane
