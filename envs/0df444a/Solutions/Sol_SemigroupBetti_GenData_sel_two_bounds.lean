-- Prove2me | solution 1 for SemigroupBetti.GenData.sel_two_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:16:40.302802+00:00
-- url     : https://prove2.me/submissions/edf1f592-8ceb-4f40-ae6f-e36822223f79

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_identity2
public import Theorems.Thm_SemigroupBetti_GenData_A_lt_B
public import Theorems.Thm_SemigroupBetti_GenData_B_lt_W
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_no_replace
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_sel_pos
public import Theorems.Thm_SemigroupBetti_GenData_two_le_W_sub_A
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
    (h2 : 2 ∈ K) : 1 ≤ G.sel d K 2 ∧ G.sel d K 2 ≤ G.W - G.A - 1 := by
  refine ⟨G.sel_pos hS hK h2, ?_⟩
  by_contra hc
  have hWA := G.two_le_W_sub_A
  have hge : G.W - G.A ≤ G.sel d K 2 := by omega
  have key : ∀ K : Finset (Fin 4), K.card = 2 → 2 ∈ K →
      (∃ k ∈ K, k ≠ 2) ∧ ((1 : Fin 4) ∉ K ∨ (3 : Fin 4) ∉ K) := by decide
  obtain ⟨⟨k, hkK, hk2⟩, h13⟩ := key K hK h2
  have hU : G.U2 ≤ G.sel d K := by
    intro i; fin_cases i <;> simp [U2, hge]
  have hUk : G.U2 k < G.sel d K k := by
    have := G.sel_pos hS hK hkK
    fin_cases k <;> simp_all [U2]
  have hAB := G.A_lt_B
  have hBW := G.B_lt_W
  rcases h13 with h1 | h3
  · exact G.no_replace hS hK hU G.identity2.1 hUk h1 (by simp [V2]; omega)
  · exact G.no_replace hS hK hU G.identity2.1 hUk h3 (by simp [V2]; omega)
end SemigroupBetti.GenData
