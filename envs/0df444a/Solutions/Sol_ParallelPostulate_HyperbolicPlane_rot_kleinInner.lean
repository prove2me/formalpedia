-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.rot_kleinInner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:15:18.058007+00:00
-- url     : https://prove2.me/submissions/095b8d71-ded1-453e-828b-6a6ae5d6889f

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
theorem _root_.solution {c s : K} (h : c ^ 2 + s ^ 2 = 1) (κ : K) (P A B : K × K) :
    kleinInner κ (rot c s P) (rot c s A) (rot c s B) = kleinInner κ P A B := by
  simp only [kleinInner, rot, cross]
  linear_combination ((A.1 - P.1) * (B.1 - P.1) + (A.2 - P.2) * (B.2 - P.2)
    + κ * (P.1 * A.2 - P.2 * A.1) * (P.1 * B.2 - P.2 * B.1) * (c ^ 2 + s ^ 2 + 1)) * h
end ParallelPostulate.HyperbolicPlane
