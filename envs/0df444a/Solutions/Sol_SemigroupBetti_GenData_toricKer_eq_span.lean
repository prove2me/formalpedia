-- Prove2me | solution 1 for SemigroupBetti.GenData.toricKer_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:14:26.206223+00:00
-- url     : https://prove2.me/submissions/53076038-aa03-4b4c-a37c-1e782a4c17d0

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
public import Theorems.Thm_SemigroupBetti_GenData_binomGens_subset_toricKer
public import Theorems.Thm_SemigroupBetti_GenData_toricKer_le_span

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution : G.toricKer K = Ideal.span (G.binomGens K : Set _) :=
  le_antisymm (G.toricKer_le_span K) (Ideal.span_le.2 (G.binomGens_subset_toricKer K))
end SemigroupBetti.GenData
