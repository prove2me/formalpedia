-- Prove2me | solution 1 for SemigroupBetti.GenData.IsSplit.compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:54:01.620782+00:00
-- url     : https://prove2.me/submissions/78b498c2-0444-4ee5-b0fd-7a0c41fc8a85

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
public import Theorems.Thm_SemigroupBetti_SharesVar_symm


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
namespace IsSplit
theorem _root_.solution {d : ℕ} {K : Finset (Fin 4)} (h : G.IsSplit d K) : G.IsSplit d Kᶜ := by
  obtain ⟨C, C', hne, hC, hC'⟩ := h
  exact ⟨C', C, hne.symm, hC', by rw [compl_compl, hC]⟩
end IsSplit
end SemigroupBetti.GenData
