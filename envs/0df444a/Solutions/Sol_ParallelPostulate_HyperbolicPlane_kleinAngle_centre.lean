-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.kleinAngle_centre
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:17:19.602772+00:00
-- url     : https://prove2.me/submissions/b0265d38-b47b-47c5-8ce9-c0f822925c67

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_kleinInner_centre
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_kleinAngle_zero_bound

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
open Real
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (κ : ℝ) (A B : ℝ × ℝ) :
    kleinAngle κ (0, 0) A B
      = InnerProductGeometry.angle (!₂[A.1, A.2] : EuclideanSpace ℝ (Fin 2)) !₂[B.1, B.2] := by
  have h : kleinAngle κ (0, 0) A B = kleinAngle 0 (0, 0) A B := by
    simp only [kleinAngle, kleinInner_centre]
  rw [h, kleinAngle_zero_bound]
  simp
end ParallelPostulate.HyperbolicPlane
