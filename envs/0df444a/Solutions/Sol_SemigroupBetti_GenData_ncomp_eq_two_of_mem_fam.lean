-- Prove2me | solution 1 for SemigroupBetti.GenData.ncomp_eq_two_of_mem_fam
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:18:56.793227+00:00
-- url     : https://prove2.me/submissions/bb9b7f49-27da-476d-8a79-9b5c1b3f7928

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
public import Theorems.Thm_SemigroupBetti_GenData_lemma5
public import Theorems.Thm_SemigroupBetti_GenData_mem_fam

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {K : Finset (Fin 4)} {d : ℕ} (h : d ∈ G.fam K) : G.ncomp d = 2 := by
  obtain ⟨-, hc, hS, -⟩ := G.mem_fam.1 h
  exact (G.lemma5 hc hS).1
end SemigroupBetti.GenData
