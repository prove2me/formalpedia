-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.realLeaningFigure_sides
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:16:04.607053+00:00
-- url     : https://prove2.me/submissions/e662f1bb-e73f-40bd-847c-b3ce9e12c284

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
open Real
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution :
    0 < realLeaningFigure.a.side realLeaningFigure.b.one ∧
      0 < realLeaningFigure.a.side realLeaningFigure.c.one := by
  refine ⟨?_, ?_⟩ <;> norm_num [realLeaningFigure, Dim.side, Dim.dir, cross]
end ParallelPostulate.HyperbolicPlane
