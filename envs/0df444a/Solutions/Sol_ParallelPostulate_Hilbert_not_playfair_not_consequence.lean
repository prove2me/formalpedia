-- Prove2me | solution 1 for ParallelPostulate.Hilbert.not_playfair_not_consequence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:19:37.613496+00:00
-- url     : https://prove2.me/submissions/06237bd2-de72-4e77-a663-25e368e3c183

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
public import Theorems.Thm_ParallelPostulate_Hilbert_euclidPlane_playfair

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.Hilbert
open Pairs HyperbolicPlane
namespace ParallelPostulate.Hilbert
theorem _root_.solution : ¬ ∀ (P L : Type) (H : HilbertPlane P L), ¬ H.Playfair :=
  fun h => h _ _ euclidPlane euclidPlane_playfair
end ParallelPostulate.Hilbert
