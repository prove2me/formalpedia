-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.step_comm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:17:46.035273+00:00
-- url     : https://prove2.me/submissions/d4a6c447-b884-4ead-b718-0a202b3c6436

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
theorem _root_.solution (κ t u : K) : step κ t u = step κ u t := by
  simp only [step]
  rw [add_comm t u, mul_assoc κ t u, mul_comm t u, ← mul_assoc]
end ParallelPostulate.HyperbolicPlane
