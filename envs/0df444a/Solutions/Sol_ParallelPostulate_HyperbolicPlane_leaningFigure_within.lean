-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.leaningFigure_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:19:15.583592+00:00
-- url     : https://prove2.me/submissions/5a3286da-1c1f-46ea-8ba4-b2abf6109734

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
    leaningFigure.a.zero ∈ plane (-1 : ℚ) ∧ leaningFigure.a.one ∈ plane (-1 : ℚ) ∧
      leaningFigure.b.one ∈ plane (-1 : ℚ) ∧ leaningFigure.c.one ∈ plane (-1 : ℚ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [leaningFigure, plane]
end ParallelPostulate.HyperbolicPlane
