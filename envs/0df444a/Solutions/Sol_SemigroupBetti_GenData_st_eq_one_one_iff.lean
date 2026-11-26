-- Prove2me | solution 1 for SemigroupBetti.GenData.st_eq_one_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:13:13.462003+00:00
-- url     : https://prove2.me/submissions/435fff0b-e34e-4f80-b1d5-26b2c8cffe07

module
public import Definitions.Def_SemigroupBetti_Antichain
public import Definitions.Def_SemigroupBetti_Arith
public import Theorems.Thm_SemigroupBetti_GenData_B_lt_W
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
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : (G.s, G.t) = (1, 1) ↔ G.A = 1 ∧ G.B = G.W - 1 := by
  have := G.B_lt_W
  simp only [Prod.mk.injEq, s, t]
  omega
end SemigroupBetti.GenData
