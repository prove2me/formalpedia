-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.step_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:15:37.931488+00:00
-- url     : https://prove2.me/submissions/131b847a-efff-4576-9370-10a291d5d508

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_step_bound

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ t u : K} (hκ : κ ≤ 0) (ht : 0 < 1 + κ * t ^ 2)
    (hu : 0 < 1 + κ * u ^ 2) : 0 < 1 + κ * step κ t u ^ 2 := by
  have h := step_den_pos hκ ht hu
  rw [step_bound h.ne']
  exact div_pos (mul_pos ht hu) (pow_pos h 2)
end ParallelPostulate.HyperbolicPlane
