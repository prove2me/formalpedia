-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.angleFigure_side_c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:12:03.140645+00:00
-- url     : https://prove2.me/submissions/efc64225-dd93-44a0-82ce-9aeef0f777e3

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
open ParallelPostulate.ThreeDimensions
open Pairs
open Real
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (β γ : ℝ) :
    (angleFigure β γ).a.side (angleFigure β γ).c.one = sin γ := by
  simp [angleFigure, Dim.side, Dim.dir, cross]
end ParallelPostulate.ThreeDimensions
