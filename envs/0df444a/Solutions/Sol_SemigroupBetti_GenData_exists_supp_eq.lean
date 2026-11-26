-- Prove2me | solution 1 for SemigroupBetti.GenData.exists_supp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:11:40.898117+00:00
-- url     : https://prove2.me/submissions/b077cf57-c81e-4f0b-a6a4-95d2c2e7379d

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
public import Theorems.Thm_SemigroupBetti_GenData_exists_full_vertex
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_supp_subset_compSupp
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
theorem _root_.solution {d : ℕ} {C : (G.nabla d).ConnectedComponent} {K : Finset (Fin 4)}
    (hK : K.card = 2) (hC : G.compSupp C = K) :
    ∃ z : G.fiber d, (G.nabla d).connectedComponentMk z = C ∧ supp z.1 = K := by
  obtain ⟨i, j, hij, rfl⟩ := card_eq_two.1 hK
  obtain ⟨z, hz, hzi, hzj⟩ := G.exists_full_vertex hij hC
  refine ⟨z, hz, Finset.Subset.antisymm (hC ▸ hz ▸ G.supp_subset_compSupp z) ?_⟩
  intro k hk
  rw [mem_insert, mem_singleton] at hk
  rcases hk with rfl | rfl <;> simpa
end SemigroupBetti.GenData
