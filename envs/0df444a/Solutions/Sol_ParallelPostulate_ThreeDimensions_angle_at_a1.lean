-- Prove2me | solution 1 for ParallelPostulate.ThreeDimensions.angle_at_a1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:17:40.727339+00:00
-- url     : https://prove2.me/submissions/b309123f-daf2-40fe-ba00-228d5a430a2e

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
public import Theorems.Thm_ParallelPostulate_ThreeDimensions_norm_toE

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.ThreeDimensions
open Pairs
open Real InnerProductGeometry
namespace ParallelPostulate.ThreeDimensions
theorem _root_.solution (β γ : ℝ) (h0 : 0 ≤ γ) (hπ : γ ≤ π) :
    angle (toE (-(angleFigure β γ).a.dir)) (toE (angleFigure β γ).c.dir) = γ := by
  rw [angle, inner_toE, norm_toE, norm_toE]
  simp [angleFigure, Dim.dir, arccos_cos h0 hπ]
end ParallelPostulate.ThreeDimensions
