-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.within_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:07.543287+00:00
-- url     : https://prove2.me/submissions/0802e644-620c-453c-93f4-a2c81f126f01

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
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
omit [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ t : K} (ht : 0 < 1 + κ * t ^ 2) : 0 < 1 + κ * (-t) ^ 2 := by
  have h : 1 + κ * (-t) ^ 2 = 1 + κ * t ^ 2 := by ring
  rw [h]
  exact ht
end ParallelPostulate.HyperbolicPlane
