-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.kleinMetric_coords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:53.748203+00:00
-- url     : https://prove2.me/submissions/de19bb03-41d3-4d52-b941-7638b7fcaa21

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
theorem _root_.solution (κ : ℝ) (p u v : ℝ × ℝ) :
    kleinMetric κ p u v
      = kleinE κ p * u.1 * v.1 + kleinF κ p * (u.1 * v.2 + u.2 * v.1) + kleinG κ p * u.2 * v.2 := by
  simp only [kleinMetric, kleinE, kleinF, kleinG, cross]
  ring
end ParallelPostulate.HyperbolicPlane
