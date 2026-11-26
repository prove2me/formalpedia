-- Prove2me | solution 1 for SemigroupBetti.GenData.sel_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:15:19.59328+00:00
-- url     : https://prove2.me/submissions/1e9a9a75-2895-4441-b260-6301adeb8665

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
    (hi : i ∈ K) : 0 < G.sel d K i := by
  rw [← mem_supp, (G.sel_of_split hS hK).2]; exact hi
end SemigroupBetti.GenData
