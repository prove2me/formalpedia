-- Prove2me | solution 1 for SemigroupBetti.GenData.nu_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:32:43.518284+00:00
-- url     : https://prove2.me/submissions/8c1b5bcb-dba4-4ffa-8177-d0f999ff1878

module
public import Mathlib
public import Definitions.Def_SemigroupBetti_Defs
public import Theorems.Thm_SemigroupBetti_mem_supp
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_pos
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_single_le_nu
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
theorem _root_.solution {z : Fin 4 → ℕ} : G.nu z = 0 ↔ z = 0 := by
  constructor
  · intro h; ext i
    have := G.single_le_nu z i
    have hp := G.n_pos i
    simp only [Pi.zero_apply]
    rw [h] at this
    exact (Nat.mul_eq_zero.1 (Nat.le_zero.1 this)).resolve_right hp.ne'
  · rintro rfl; simp
end SemigroupBetti.GenData
