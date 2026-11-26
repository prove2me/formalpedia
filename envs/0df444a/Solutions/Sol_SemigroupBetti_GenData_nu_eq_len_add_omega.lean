-- Prove2me | solution 1 for SemigroupBetti.GenData.nu_eq_len_add_omega
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:29.411996+00:00
-- url     : https://prove2.me/submissions/44f79729-e691-4f99-ab78-7c9a53311f48

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_mem_supp
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_nu_eq_sum
attribute [local simp] SemigroupBetti.mem_supp
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_three

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution (z : Fin 4 → ℕ) : G.nu z = G.m * len z + G.omega z := by
  rw [nu_eq_sum]; simp only [len, omega, Fin.sum_univ_four]; ring
end SemigroupBetti.GenData
