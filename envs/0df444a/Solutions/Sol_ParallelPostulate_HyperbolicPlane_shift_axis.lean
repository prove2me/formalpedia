-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.shift_axis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:04.215075+00:00
-- url     : https://prove2.me/submissions/2d23fe81-406b-4a9f-9c28-41f222c0c79f

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
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (κ a w t : K) : shift κ a w (t, 0) = (step κ t a, 0) := by
  simp only [shift, step, mul_zero, zero_div]
  rw [mul_assoc κ a t, mul_comm a t, ← mul_assoc]
end ParallelPostulate.HyperbolicPlane
