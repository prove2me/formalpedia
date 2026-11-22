-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.shift_centre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:02.498538+00:00
-- url     : https://prove2.me/submissions/a3cda94a-60f2-42b8-b5b4-881ee90073b2

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
theorem _root_.solution (κ a w : K) : shift κ a w (0, 0) = (a, 0) := by
  simp [shift]
end ParallelPostulate.HyperbolicPlane
