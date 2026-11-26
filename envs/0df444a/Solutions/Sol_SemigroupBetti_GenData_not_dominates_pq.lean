-- Prove2me | solution 1 for SemigroupBetti.GenData.not_dominates_pq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:17:10.218858+00:00
-- url     : https://prove2.me/submissions/9449d527-ed94-4287-b08f-ea83bb049773

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_GenData_isSplit12_of_mem_famE
public import Theorems.Thm_SemigroupBetti_GenData_identity3
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_no_replace
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_p_pos
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
theorem _root_.solution {d : ℕ} (hd : d ∈ G.famE) (hu : G.p ≤ G.sel d {1, 2} 1)
    (hv : G.q ≤ G.sel d {1, 2} 2) (hne : (G.sel d {1, 2} 1, G.sel d {1, 2} 2) ≠ (G.p, G.q)) :
    False := by
  have hS := G.isSplit12_of_mem_famE hd
  have hK : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
  have hU : G.U3 ≤ G.sel d {1, 2} := by
    intro i; fin_cases i <;> simp [U3, hu, hv]
  have hp := G.p_pos
  by_cases h1 : G.p < G.sel d {1, 2} 1
  · exact G.no_replace hS hK hU G.identity3.1 (k := 1) (by simpa [U3] using h1)
      (j := 0) (by decide) (by simp [V3]; omega)
  · have h2 : G.q < G.sel d {1, 2} 2 := by
      by_contra h2
      exact hne (Prod.ext (by simp only; omega) (by simp only; omega))
    exact G.no_replace hS hK hU G.identity3.1 (k := 2) (by simpa [U3] using h2)
      (j := 0) (by decide) (by simp [V3]; omega)
end SemigroupBetti.GenData
