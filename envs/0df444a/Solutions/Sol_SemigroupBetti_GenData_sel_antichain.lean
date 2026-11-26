-- Prove2me | solution 1 for SemigroupBetti.GenData.sel_antichain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:15:31.206451+00:00
-- url     : https://prove2.me/submissions/00cd53ba-cfba-4780-893a-82049aba27d0

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
public import Theorems.Thm_SemigroupBetti_SharesVar_symm
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
theorem _root_.solution {K : Finset (Fin 4)} (hK : K.card = 2) {d d' : ℕ} (hS : G.IsSplit d K)
    (hS' : G.IsSplit d' K) (hne : d ≠ d') : ¬ G.sel d K ≤ G.sel d' K := by
  intro hle
  have hz := G.sel_of_split hS hK
  have hz' := G.sel_of_split hS' hK
  have hKc := card_compl_of_card_two hK
  have hy := G.sel_of_split hS.compl hKc
  have hy' := G.sel_of_split hS'.compl hKc
  set z := G.sel d K
  set z' := G.sel d' K
  set y := G.sel d Kᶜ
  set y' := G.sel d' Kᶜ
  -- `δ = z' - z ≠ 0`
  have hδ : ∃ i, z i < z' i := by
    by_contra h
    push Not at h
    apply hne
    rw [← hz.1, ← hz'.1]
    congr 1
    funext i; exact le_antisymm (hle i) (h i)
  obtain ⟨i, hi⟩ := hδ
  have hiK : i ∈ K := hz'.2 ▸ mem_supp.2 (by omega)
  obtain ⟨j, hj⟩ : Kᶜ.Nonempty := card_pos.1 (by omega)
  have hyj : 0 < y j := by rw [← mem_supp, hy.2]; exact hj
  have hy'j : 0 < y' j := by rw [← mem_supp, hy'.2]; exact hj
  have hb : G.nu (z' - z + y) = d' := by
    rw [G.nu_replace hle (hz.1.trans hy.1.symm), hz'.1]
  refine G.no_bridge hS' hz'.1 hy'.1 hb hiK (by omega) (mem_compl.1 hj) hy'j
    ⟨i, ?_, by omega⟩ ⟨j, ?_, hy'j⟩
  · simp only [Pi.add_apply, Pi.sub_apply]; omega
  · simp only [Pi.add_apply, Pi.sub_apply]; omega
end SemigroupBetti.GenData
