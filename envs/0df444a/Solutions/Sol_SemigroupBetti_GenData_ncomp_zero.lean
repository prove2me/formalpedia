-- Prove2me | solution 1 for SemigroupBetti.GenData.ncomp_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:06:04.572829+00:00
-- url     : https://prove2.me/submissions/41ce25df-4058-4133-964f-d87573d6df82

module
public import Definitions.Def_SemigroupBetti_Defs
public import Definitions.Def_SemigroupBetti_Fiber
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_fiber_zero
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
theorem _root_.solution : G.ncomp 0 = 1 := by
  unfold ncomp
  have : Unique (G.fiber 0) := by
    rw [fiber_zero]; exact ⟨⟨⟨0, by simp⟩⟩, fun ⟨x, hx⟩ => by simp at hx; simp [hx]⟩
  rw [Fintype.card_eq_one_iff]
  exact ⟨(G.nabla 0).connectedComponentMk default, SimpleGraph.ConnectedComponent.ind
    fun v => by rw [Subsingleton.elim v default]⟩
end SemigroupBetti.GenData
