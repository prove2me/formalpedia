-- Prove2me | solution 1 for ParallelPostulate.Hilbert.playfair_independent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:19:34.104922+00:00
-- url     : https://prove2.me/submissions/2784f342-6e71-4fd7-87ed-7afc5b9db880

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
public import Theorems.Thm_ParallelPostulate_Hilbert_kleinPlane_not_playfair

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.Hilbert
open Pairs HyperbolicPlane
namespace ParallelPostulate.Hilbert
theorem _root_.solution :
    (∃ (P L : Type) (H : HilbertPlane P L), H.Playfair) ∧
      ∃ (P L : Type) (H : HilbertPlane P L), ¬ H.Playfair :=
  ⟨⟨_, _, euclidPlane, euclidPlane_playfair⟩, ⟨_, _, kleinPlane, kleinPlane_not_playfair⟩⟩
end ParallelPostulate.Hilbert
