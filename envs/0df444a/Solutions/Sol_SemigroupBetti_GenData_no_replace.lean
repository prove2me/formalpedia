-- Prove2me | solution 1 for SemigroupBetti.GenData.no_replace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:15:29.899402+00:00
-- url     : https://prove2.me/submissions/c43db386-a702-4b5f-b584-5e2db0dc8fe2

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
public import Theorems.Thm_SemigroupBetti_GenData_IsSplit_compl
public import Theorems.Thm_SemigroupBetti_GenData_no_bridge
public import Theorems.Thm_SemigroupBetti_GenData_sel_of_split
public import Theorems.Thm_SemigroupBetti_GenData_card_compl_of_card_two
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_replace
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.mem_fiber
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} {K : Finset (Fin 4)} (hS : G.IsSplit d K) (hK : K.card = 2)
    {U V : Fin 4 → ℕ} (hUz : U ≤ G.sel d K) (hUV : G.nu U = G.nu V) {k j : Fin 4}
    (hk : U k < G.sel d K k) (hj : j ∉ K) (hVj : 0 < V j) : False := by
  have hz := G.sel_of_split hS hK
  have hy := G.sel_of_split hS.compl (card_compl_of_card_two hK)
  have hkK : k ∈ K := hz.2 ▸ mem_supp.2 (by omega)
  have hyj : 0 < G.sel d Kᶜ j := by rw [← mem_supp, hy.2]; exact mem_compl.2 hj
  refine G.no_bridge hS hz.1 hy.1 ((G.nu_replace hUz hUV).trans hz.1) hkK (by omega) hj hyj
    ⟨k, ?_, by omega⟩ ⟨j, ?_, hyj⟩
  · simp only [Pi.add_apply, Pi.sub_apply]; omega
  · simp only [Pi.add_apply, Pi.sub_apply]; omega
end SemigroupBetti.GenData
