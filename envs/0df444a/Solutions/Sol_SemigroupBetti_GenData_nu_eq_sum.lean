-- Prove2me | solution 1 for SemigroupBetti.GenData.nu_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:27:32.681412+00:00
-- url     : https://prove2.me/submissions/f455e01f-1888-46fd-b82a-ea4651731673

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_mem_supp
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_three
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
theorem _root_.solution (z : Fin 4 → ℕ) : G.nu z = z 0 * G.m + z 1 * (G.m + G.a) +
    z 2 * (G.m + G.b) + z 3 * (G.m + G.w) := by
  simp [nu, Fin.sum_univ_four]
end SemigroupBetti.GenData
