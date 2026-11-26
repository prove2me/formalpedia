-- Prove2me | solution 1 for SemigroupBetti.GenData.isSplit12_of_mem_famE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:57:12.321605+00:00
-- url     : https://prove2.me/submissions/e5859e3d-378f-4791-930e-61c5fff84be3

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_GenData_isSplit_of_mem_fam
public import Theorems.Thm_SemigroupBetti_GenData_IsSplit_compl


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} (h : d ∈ G.famE) : G.IsSplit d {1, 2} := by
  have hc : ({0, 3} : Finset (Fin 4))ᶜ = {1, 2} := by decide
  exact hc ▸ (G.isSplit_of_mem_fam h).compl
end SemigroupBetti.GenData
