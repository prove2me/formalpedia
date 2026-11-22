-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.det_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:13:21.193493+00:00
-- url     : https://prove2.me/submissions/371151a8-8d22-405f-8377-4c6975a68752

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
open Filter Topology
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (a b c d e f g h i : ℝ) :
    Matrix.det !![a, b, c; d, e, f; g, h, i]
      = a * e * i - a * f * h - b * d * i + b * f * g + c * d * h - c * e * g := by
  rw [Matrix.det_fin_three]
  simp
end ParallelPostulate.HyperbolicPlane
