-- Prove2me | solution 1 for ParallelPostulate.Hilbert.playfair_not_consequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:19:35.976492+00:00
-- url     : https://prove2.me/submissions/c7e99020-2862-45d5-8d03-365e5ff0d4ca

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
public import Theorems.Thm_ParallelPostulate_Hilbert_kleinPlane_not_playfair

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.Hilbert
open Pairs HyperbolicPlane
namespace ParallelPostulate.Hilbert
theorem _root_.solution : ¬ ∀ (P L : Type) (H : HilbertPlane P L), H.Playfair :=
  fun h => kleinPlane_not_playfair (h _ _ kleinPlane)
end ParallelPostulate.Hilbert
