-- Prove2me | solution 1 for SemigroupBetti.GenData.sel_one_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:16:39.73908+00:00
-- url     : https://prove2.me/submissions/207e6b78-5b62-4614-821f-c37cfa92cdde

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_identity1
public import Theorems.Thm_SemigroupBetti_GenData_A_lt_B
public import Theorems.Thm_SemigroupBetti_GenData_A_pos
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_no_replace
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_sel_pos
public import Theorems.Thm_SemigroupBetti_GenData_two_le_B
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
    (h1 : 1 ∈ K) : 1 ≤ G.sel d K 1 ∧ G.sel d K 1 ≤ G.B - 1 := by
  refine ⟨G.sel_pos hS hK h1, ?_⟩
  by_contra hc
  have hB := G.two_le_B
  have hge : G.B ≤ G.sel d K 1 := by omega
  have key : ∀ K : Finset (Fin 4), K.card = 2 → 1 ∈ K →
      (∃ k ∈ K, k ≠ 1) ∧ ((0 : Fin 4) ∉ K ∨ (2 : Fin 4) ∉ K) := by decide
  obtain ⟨⟨k, hkK, hk1⟩, h02⟩ := key K hK h1
  have hU : G.U1 ≤ G.sel d K := by
    intro i; fin_cases i <;> simp [U1, hge]
  have hUk : G.U1 k < G.sel d K k := by
    have := G.sel_pos hS hK hkK
    fin_cases k <;> simp_all [U1]
  have hAB := G.A_lt_B
  have hA := G.A_pos
  rcases h02 with h0 | h2
  · exact G.no_replace hS hK hU G.identity1.1 hUk h0 (by simp [V1]; omega)
  · exact G.no_replace hS hK hU G.identity1.1 hUk h2 (by simp [V1]; omega)
end SemigroupBetti.GenData
