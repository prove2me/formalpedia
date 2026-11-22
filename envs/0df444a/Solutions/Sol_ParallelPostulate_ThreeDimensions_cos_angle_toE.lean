-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.cos_angle_toE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:14:16.065249+00:00
-- url     : https://prove2.me/submissions/2c95fcf0-182b-428c-b1de-bbdb5a38649f

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
    cos (angle (toE p) (toE q)) * (‖toE p‖ * ‖toE q‖) = p.1 * q.1 + p.2 * q.2 := by
  rw [cos_angle_mul_norm_mul_norm, inner_toE]
end ParallelPostulate.ThreeDimensions
