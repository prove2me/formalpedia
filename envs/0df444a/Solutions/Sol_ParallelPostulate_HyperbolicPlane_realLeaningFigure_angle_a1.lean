-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.realLeaningFigure_angle_a1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:16:05.620532+00:00
-- url     : https://prove2.me/submissions/26689c23-b205-4f27-afe6-b298cf972349

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
    kleinAngle (-1) realLeaningFigure.a.one realLeaningFigure.a.zero realLeaningFigure.c.one
      = arccos (3 / √409) := by
  have h : kleinInner (-1) realLeaningFigure.a.one realLeaningFigure.a.zero
      realLeaningFigure.c.one = 9 / 250 := by
    norm_num [realLeaningFigure, kleinInner, cross]
  have h1 : kleinInner (-1) realLeaningFigure.a.one realLeaningFigure.a.zero
      realLeaningFigure.a.zero = (3 / 5) ^ 2 := by
    norm_num [realLeaningFigure, kleinInner, cross]
  have h2 : kleinInner (-1) realLeaningFigure.a.one realLeaningFigure.c.one
      realLeaningFigure.c.one = 409 / 50 ^ 2 := by
    norm_num [realLeaningFigure, kleinInner, cross]
  have hs : 0 < √409 := by positivity
  rw [kleinAngle, h, h1, h2, sqrt_sq (by norm_num), sqrt_div' _ (by norm_num),
    sqrt_sq (by norm_num)]
  congr 1
  field_simp
  norm_num
end ParallelPostulate.HyperbolicPlane
