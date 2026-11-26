-- Prove2me | solution 1 for SemigroupBetti.GenData.sel_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:15:22.341878+00:00
-- url     : https://prove2.me/submissions/02abb92c-522e-4308-a8cc-48d2d427bdf0

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
public import Theorems.Thm_SemigroupBetti_GenData_sel_of_split
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.mem_supp



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2) {i : Fin 4}
    (hi : i ∉ K) : G.sel d K i = 0 := by
  by_contra h
  exact hi ((G.sel_of_split hS hK).2 ▸ mem_supp.2 (Nat.pos_of_ne_zero h))
end SemigroupBetti.GenData
