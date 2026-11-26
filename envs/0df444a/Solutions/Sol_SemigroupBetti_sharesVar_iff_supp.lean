-- Prove2me | solution 1 for SemigroupBetti.sharesVar_iff_supp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:15.816539+00:00
-- url     : https://prove2.me/submissions/8f4052a6-6156-43d3-8b5a-862cb6239ede

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.mem_supp

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
namespace SemigroupBetti
theorem _root_.solution {z z' : Fin 4 → ℕ} :
    SharesVar z z' ↔ ¬ Disjoint (supp z) (supp z') := by
  simp only [SharesVar, Finset.not_disjoint_iff, mem_supp]
end SemigroupBetti
