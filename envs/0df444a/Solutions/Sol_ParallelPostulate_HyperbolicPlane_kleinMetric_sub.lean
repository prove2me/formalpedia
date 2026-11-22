-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.kleinMetric_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:13:14.382208+00:00
-- url     : https://prove2.me/submissions/e1d4ef3a-6fd7-4ebc-9e9c-82d1cc91b699

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
theorem _root_.solution (κ : K) (P A B : K × K) :
    kleinMetric κ P (A - P) (B - P)
      = kleinInner κ P A B / (1 + κ * (P.1 ^ 2 + P.2 ^ 2)) ^ 2 := by
  simp only [kleinMetric, kleinInner, cross, Prod.fst_sub, Prod.snd_sub]
  ring
end ParallelPostulate.HyperbolicPlane
