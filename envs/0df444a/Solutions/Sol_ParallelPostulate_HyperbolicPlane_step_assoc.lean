-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.step_assoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:18:18.911588+00:00
-- url     : https://prove2.me/submissions/01536977-e336-4a2b-bcb4-c3d685beba6c

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_step_within
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ t u v : K} (hκ : κ ≤ 0) (ht : 0 < 1 + κ * t ^ 2)
    (hu : 0 < 1 + κ * u ^ 2) (hv : 0 < 1 + κ * v ^ 2) :
    step κ (step κ t u) v = step κ t (step κ u v) := by
  have h1 := (step_den_pos hκ ht hu).ne'
  have h2 := (step_den_pos hκ hu hv).ne'
  have h3 := (step_den_pos hκ (step_within hκ ht hu) hv).ne'
  have h4 := (step_den_pos hκ ht (step_within hκ hu hv)).ne'
  have hX : step κ t u * (1 - κ * t * u) = t + u := div_mul_cancel₀ _ h1
  have hY : step κ u v * (1 - κ * u * v) = u + v := div_mul_cancel₀ _ h2
  have hL : step κ (step κ t u) v * (1 - κ * step κ t u * v) = step κ t u + v :=
    div_mul_cancel₀ _ h3
  have hR : step κ t (step κ u v) * (1 - κ * t * step κ u v) = t + step κ u v :=
    div_mul_cancel₀ _ h4
  have e3 : (1 - κ * step κ t u * v) * (1 - κ * t * u)
      = 1 - κ * (t * u + t * v + u * v) := by
    linear_combination -κ * v * hX
  have e4 : (1 - κ * t * step κ u v) * (1 - κ * u * v)
      = 1 - κ * (t * u + t * v + u * v) := by
    linear_combination -κ * t * hY
  have eL : step κ (step κ t u) v * (1 - κ * (t * u + t * v + u * v))
      = t + u + v - κ * t * u * v := by
    rw [← e3]
    linear_combination (1 - κ * t * u) * hL + hX
  have eR : step κ t (step κ u v) * (1 - κ * (t * u + t * v + u * v))
      = t + u + v - κ * t * u * v := by
    rw [← e4]
    linear_combination (1 - κ * u * v) * hR + hY
  have hE : 1 - κ * (t * u + t * v + u * v) ≠ 0 := by
    rw [← e3]
    exact mul_ne_zero h3 h1
  exact mul_right_cancel₀ hE (eL.trans eR.symm)
end ParallelPostulate.HyperbolicPlane
