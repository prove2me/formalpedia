-- Prove2me | solution 1 for SemigroupBetti.GenData.identity1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:11:50.975333+00:00
-- url     : https://prove2.me/submissions/f86e025a-dfe5-4d68-8824-d8ddfbd9dffc

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_nu_vec
public import Theorems.Thm_SemigroupBetti_GenData_len_vec
public import Theorems.Thm_SemigroupBetti_GenData_A_lt_B
public import Theorems.Thm_SemigroupBetti_GenData_a_eq
public import Theorems.Thm_SemigroupBetti_GenData_b_eq
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
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
theorem _root_.solution : G.nu G.U1 = G.nu G.V1 ∧ len G.U1 = len G.V1 ∧ len G.U1 = G.B := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le G.A_lt_B.le
  have e1 : G.B - G.A = k := by omega
  simp only [U1, V1, nu_vec, len_vec, e1]
  refine ⟨?_, by omega, by omega⟩
  rw [G.a_eq, G.b_eq, hk]; ring
end SemigroupBetti.GenData
