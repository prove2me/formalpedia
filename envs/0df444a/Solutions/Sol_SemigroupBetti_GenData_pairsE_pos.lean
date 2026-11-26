-- Prove2me | solution 1 for SemigroupBetti.GenData.pairsE_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:17:19.741058+00:00
-- url     : https://prove2.me/submissions/e6d15a75-a18f-45ac-be99-441086fe6f7a

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_GenData_isSplit12_of_mem_famE
public import Theorems.Thm_SemigroupBetti_GenData_sel_pos


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : ∀ x ∈ G.pairsE, 1 ≤ x.1 ∧ 1 ≤ x.2 := by
  intro x hx
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  have hK : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
  exact ⟨G.sel_pos (G.isSplit12_of_mem_famE hd) hK (by decide),
    G.sel_pos (G.isSplit12_of_mem_famE hd) hK (by decide)⟩
end SemigroupBetti.GenData
