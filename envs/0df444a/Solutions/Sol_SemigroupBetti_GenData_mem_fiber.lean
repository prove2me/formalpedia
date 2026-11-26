-- Prove2me | solution 1 for SemigroupBetti.GenData.mem_fiber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:50:45.910317+00:00
-- url     : https://prove2.me/submissions/f939f11f-e27a-4eeb-a3db-cab3c039e73d

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_le_div_m_of_nu_eq
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



set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open Finset
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution {d : ℕ} {z : Fin 4 → ℕ} : z ∈ G.fiber d ↔ G.nu z = d := by
  simp only [fiber, mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro h i; exact Nat.lt_succ_of_le (G.le_div_m_of_nu_eq h i)
end SemigroupBetti.GenData
