-- Prove2me | solution 1 for SemigroupBetti.GenData.pairsE_antichain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:18:08.869772+00:00
-- url     : https://prove2.me/submissions/4de5f444-ce64-4f5b-bf85-3c5dccad62e1

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_GenData_isSplit12_of_mem_famE
public import Theorems.Thm_SemigroupBetti_GenData_sel12_le_iff
public import Theorems.Thm_SemigroupBetti_GenData_sel_antichain


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : IsPairAntichain G.pairsE := by
  intro x hx y hy h1 h2
  obtain ⟨d, hd, rfl⟩ := mem_image.1 hx
  obtain ⟨d', hd', rfl⟩ := mem_image.1 hy
  have hK : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
  by_cases hne : d = d'
  · rw [hne]
  · exact absurd ((G.sel12_le_iff hd hd').2 ⟨h1, h2⟩)
      (G.sel_antichain hK (G.isSplit12_of_mem_famE hd) (G.isSplit12_of_mem_famE hd') hne)
end SemigroupBetti.GenData
