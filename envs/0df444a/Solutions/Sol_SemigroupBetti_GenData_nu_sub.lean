-- Prove2me | solution 1 for SemigroupBetti.GenData.nu_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:29:12.461138+00:00
-- url     : https://prove2.me/submissions/bd0ed39a-5280-46ea-9b45-283bab20eed4

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_mem_supp
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_add
attribute [local simp] SemigroupBetti.mem_supp
attribute [local simp] SemigroupBetti.GenData.n_zero
attribute [local simp] SemigroupBetti.GenData.n_one
attribute [local simp] SemigroupBetti.GenData.n_two
attribute [local simp] SemigroupBetti.GenData.n_three
attribute [local simp] SemigroupBetti.GenData.nu_zero

set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {x y : Fin 4 → ℕ} (h : x ≤ y) : G.nu y = G.nu x + G.nu (y - x) := by
  rw [← nu_add]; congr 1; ext i; simp only [Pi.add_apply, Pi.sub_apply]
  have hi : x i ≤ y i := h i
  omega
end SemigroupBetti.GenData
