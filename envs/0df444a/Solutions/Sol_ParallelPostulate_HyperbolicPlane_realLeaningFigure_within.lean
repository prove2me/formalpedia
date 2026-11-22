-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.realLeaningFigure_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:16:02.993248+00:00
-- url     : https://prove2.me/submissions/131b6afa-397a-4350-835a-d775529f1b03

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
    realLeaningFigure.a.zero ∈ plane (-1 : ℝ) ∧ realLeaningFigure.a.one ∈ plane (-1 : ℝ) ∧
      realLeaningFigure.b.one ∈ plane (-1 : ℝ) ∧ realLeaningFigure.c.one ∈ plane (-1 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [realLeaningFigure, plane]
end ParallelPostulate.HyperbolicPlane
