-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.sin_angle_toE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:12:43.939268+00:00
-- url     : https://prove2.me/submissions/76228fec-d49d-4126-9f28-f39cafd614e0

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_inner_toE

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
open Real InnerProductGeometry
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (p q : ℝ × ℝ) :
    sin (angle (toE p) (toE q)) * (‖toE p‖ * ‖toE q‖) = |cross p q| := by
  rw [sin_angle_mul_norm_mul_norm, inner_toE, inner_toE, inner_toE, ← sqrt_sq_eq_abs]
  congr 1
  simp only [cross]
  ring
end ParallelPostulate.ThreeDimensions
