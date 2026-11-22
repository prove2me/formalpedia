-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.realLeaningFigure_angles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:02.031419+00:00
-- url     : https://prove2.me/submissions/cd77489d-9d5b-4348-b53d-61e14276d45a

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_realLeaningFigure_angle_a0
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_realLeaningFigure_angle_a1_lt

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
      + kleinAngle (-1) realLeaningFigure.a.one realLeaningFigure.a.zero realLeaningFigure.c.one
      < π := by
  rw [realLeaningFigure_angle_a0]
  linarith [realLeaningFigure_angle_a1_lt]
end ParallelPostulate.HyperbolicPlane
