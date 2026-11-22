-- Prove2me | solution 1 for ParallelPostulate.Hilbert.playfair_independent_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:19:38.424903+00:00
-- url     : https://prove2.me/submissions/243169e3-bfda-4112-8753-5d729313c7d6

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
public import Theorems.Thm_ParallelPostulate_Hilbert_model_dedekind
public import Theorems.Thm_ParallelPostulate_Hilbert_model_archimedes
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
    (∃ (P L : Type) (H : HilbertPlane P L), H.Archimedes ∧ H.Dedekind ∧ H.Playfair) ∧
      ∃ (P L : Type) (H : HilbertPlane P L), H.Archimedes ∧ H.Dedekind ∧ ¬ H.Playfair :=
  ⟨⟨_, _, euclidPlane, model_archimedes 0 le_rfl, model_dedekind 0 le_rfl, euclidPlane_playfair⟩,
    ⟨_, _, kleinPlane, model_archimedes (-1) (by norm_num), model_dedekind (-1) (by norm_num),
      kleinPlane_not_playfair⟩⟩
end ParallelPostulate.Hilbert
