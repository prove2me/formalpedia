-- Prove2me | solution 1 for SemigroupBetti.GenData.identity2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:58:23.770837+00:00
-- url     : https://prove2.me/submissions/4d392466-aa55-490c-ae1e-e40936367754

module
public import Definitions.Def_SemigroupBetti_Partition
public import Definitions.Def_SemigroupBetti_Identities
public import Theorems.Thm_SemigroupBetti_GenData_nu_vec
public import Theorems.Thm_SemigroupBetti_GenData_len_vec
public import Theorems.Thm_SemigroupBetti_GenData_A_lt_B
public import Theorems.Thm_SemigroupBetti_GenData_B_lt_W
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
theorem _root_.solution : G.nu G.U2 = G.nu G.V2 ∧ len G.U2 = len G.V2 ∧ len G.U2 = G.W - G.A := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le G.A_lt_B.le
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le G.B_lt_W.le
  have e1 : G.B - G.A = k := by omega
  have e2 : G.W - G.B = l := by omega
  have e3 : G.W - G.A = k + l := by omega
  simp only [U2, V2, nu_vec, len_vec, e1, e2, e3]
  refine ⟨?_, by omega, by omega⟩
  rw [G.a_eq, G.b_eq, G.w_eq, hl, hk]; ring
end SemigroupBetti.GenData
