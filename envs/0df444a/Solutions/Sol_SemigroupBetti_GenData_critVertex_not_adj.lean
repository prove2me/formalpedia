-- Prove2me | solution 1 for SemigroupBetti.GenData.critVertex_not_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:08:24.595483+00:00
-- url     : https://prove2.me/submissions/9d3a9315-b9e1-4ada-80a4-869ee0d7dafb

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
public import Theorems.Thm_SemigroupBetti_GenData_alt_coord_eq_zero
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_SharesVar_symm
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
theorem _root_.solution (i : Fin 4) (z : G.fiber (G.crit i * G.n i)) :
    ¬ (G.nabla _).Adj (G.critVertex i) z := by
  rintro ⟨hne, k, hk, hzk⟩
  have hki : k = i := by
    by_contra h; simp [critVertex, h] at hk
  subst hki
  have hz : z.1 ≠ Pi.single k (G.crit k) := fun h => hne (Subtype.ext h.symm)
  have := G.alt_coord_eq_zero (G.mem_fiber.1 z.2) hz
  omega
end SemigroupBetti.GenData
