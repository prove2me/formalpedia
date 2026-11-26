-- Prove2me | solution 1 for SemigroupBetti.GenData.identity3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:13:05.843917+00:00
-- url     : https://prove2.me/submissions/863f220d-81a5-4b95-814c-add64eba5b04

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_W_eq_B_add_t
public import Theorems.Thm_SemigroupBetti_GenData_p_mul_A
public import Theorems.Thm_SemigroupBetti_GenData_nu_vec
public import Theorems.Thm_SemigroupBetti_GenData_len_vec
public import Theorems.Thm_SemigroupBetti_GenData_a_eq
public import Theorems.Thm_SemigroupBetti_GenData_b_eq
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_w_eq
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
theorem _root_.solution : G.nu G.U3 = G.nu G.V3 ∧ len G.U3 = len G.V3 ∧ len G.U3 = G.p + G.q := by
  simp only [U3, V3, nu_vec, len_vec]
  refine ⟨?_, by omega, by omega⟩
  have h := G.p_mul_A
  rw [G.a_eq, G.b_eq, G.w_eq, G.W_eq_B_add_t]
  linear_combination G.g * h
end SemigroupBetti.GenData
