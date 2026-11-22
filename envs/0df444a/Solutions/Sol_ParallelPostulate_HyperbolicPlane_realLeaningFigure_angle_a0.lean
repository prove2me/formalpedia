-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.realLeaningFigure_angle_a0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:16:05.059573+00:00
-- url     : https://prove2.me/submissions/949fbbc1-5ebe-4236-a478-c844cff179cb

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
    kleinAngle (-1) realLeaningFigure.a.zero realLeaningFigure.a.one realLeaningFigure.b.one
      = π / 2 := by
  have h : kleinInner (-1) realLeaningFigure.a.zero realLeaningFigure.a.one
      realLeaningFigure.b.one = 0 := by
    norm_num [realLeaningFigure, kleinInner, cross]
  rw [kleinAngle, h, zero_div, arccos_zero]
end ParallelPostulate.HyperbolicPlane
