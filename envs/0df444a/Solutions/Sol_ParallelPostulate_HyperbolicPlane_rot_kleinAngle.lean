-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.rot_kleinAngle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:16:37.501923+00:00
-- url     : https://prove2.me/submissions/46eeb654-ca0f-4f9b-b4c9-2e182c8558c0

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_rot_kleinInner

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
open Real
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) (κ : ℝ) (P A B : ℝ × ℝ) :
    kleinAngle κ (rot c s P) (rot c s A) (rot c s B) = kleinAngle κ P A B := by
  simp only [kleinAngle, rot_kleinInner h]
end ParallelPostulate.HyperbolicPlane
