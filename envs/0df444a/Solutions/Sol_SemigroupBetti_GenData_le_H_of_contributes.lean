-- Prove2me | solution 1 for SemigroupBetti.GenData.le_H_of_contributes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:09:46.668743+00:00
-- url     : https://prove2.me/submissions/a8cf01b8-12e3-4df2-b778-c03e763143a9

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_exists_not_reachable
public import Theorems.Thm_SemigroupBetti_GenData_coord_le_of_contributes
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_mem_supp
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.nu_zero
attribute [local simp] SemigroupBetti.mem_supp


attribute [local simp] SemigroupBetti.GenData.mem_fiber

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} (h : G.contributes d) : d ≤ G.H := by
  obtain ⟨z, -, -⟩ := G.exists_not_reachable h
  rw [← G.mem_fiber.1 z.2, nu, H, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (G.coord_le_of_contributes h z i)
end SemigroupBetti.GenData
