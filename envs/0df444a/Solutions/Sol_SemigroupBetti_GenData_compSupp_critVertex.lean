-- Prove2me | solution 1 for SemigroupBetti.GenData.compSupp_critVertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:10:34.414858+00:00
-- url     : https://prove2.me/submissions/f5126b41-d585-47d1-bdbd-8b4b421eca8b

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
public import Theorems.Thm_SemigroupBetti_GenData_one_le_crit
public import Theorems.Thm_SemigroupBetti_GenData_eq_critVertex_of_reachable
public import Theorems.Thm_SemigroupBetti_GenData_mem_compSupp
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
theorem _root_.solution (i : Fin 4) :
    G.compSupp ((G.nabla _).connectedComponentMk (G.critVertex i)) = {i} := by
  ext k
  rw [mem_compSupp, mem_singleton]
  constructor
  · rintro ⟨z, hz, hzk⟩
    have := G.eq_critVertex_of_reachable i (SimpleGraph.ConnectedComponent.exact hz).symm
    subst this
    by_contra h; simp [critVertex, h] at hzk
  · intro h
    rw [h]
    exact ⟨G.critVertex i, rfl, by simpa [critVertex] using Nat.lt_of_lt_of_le Nat.zero_lt_one (G.one_le_crit i)⟩
end SemigroupBetti.GenData
