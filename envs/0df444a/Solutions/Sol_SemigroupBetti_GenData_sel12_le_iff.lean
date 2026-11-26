-- Prove2me | solution 1 for SemigroupBetti.GenData.sel12_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:16:43.863822+00:00
-- url     : https://prove2.me/submissions/806b9b93-1df6-409a-8f28-05e41ceacf74

module
public import Definitions.Def_SemigroupBetti_Identities
public import Definitions.Def_SemigroupBetti_Antichain
public import Theorems.Thm_SemigroupBetti_GenData_isSplit12_of_mem_famE
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_sel_eq_zero
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
theorem _root_.solution {d d' : ℕ} (hd : d ∈ G.famE) (hd' : d' ∈ G.famE) :
    G.sel d {1, 2} ≤ G.sel d' {1, 2} ↔
      G.sel d {1, 2} 1 ≤ G.sel d' {1, 2} 1 ∧ G.sel d {1, 2} 2 ≤ G.sel d' {1, 2} 2 := by
  have hK : ({1, 2} : Finset (Fin 4)).card = 2 := by decide
  have hS := G.isSplit12_of_mem_famE hd
  have hS' := G.isSplit12_of_mem_famE hd'
  constructor
  · intro h; exact ⟨h 1, h 2⟩
  · rintro ⟨h1, h2⟩ i
    fin_cases i
    · simp [G.sel_eq_zero hS hK (i := 0) (by decide)]
    · exact h1
    · exact h2
    · simp [G.sel_eq_zero hS hK (i := 3) (by decide)]
end SemigroupBetti.GenData
