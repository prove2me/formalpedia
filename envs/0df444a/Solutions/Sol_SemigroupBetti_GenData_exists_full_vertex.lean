-- Prove2me | solution 1 for SemigroupBetti.GenData.exists_full_vertex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:10:35.159817+00:00
-- url     : https://prove2.me/submissions/f8c6895b-8b13-4dab-8d8e-256abd4fc514

module
public import Definitions.Def_SemigroupBetti_Critical
public import Definitions.Def_SemigroupBetti_Partition
public import Theorems.Thm_SemigroupBetti_reachable_induction
public import Theorems.Thm_SemigroupBetti_GenData_mem_compSupp
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_supp_subset_compSupp
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
theorem _root_.solution {d : ℕ} {C : (G.nabla d).ConnectedComponent} {i j : Fin 4}
    (hij : i ≠ j) (hC : G.compSupp C = {i, j}) :
    ∃ z : G.fiber d, (G.nabla d).connectedComponentMk z = C ∧ 0 < z.1 i ∧ 0 < z.1 j := by
  by_contra H
  push Not at H
  obtain ⟨z0, hz0, hz0i⟩ := G.mem_compSupp.1 (show i ∈ G.compSupp C by rw [hC]; simp)
  obtain ⟨z1, hz1, hz1j⟩ := G.mem_compSupp.1 (show j ∈ G.compSupp C by rw [hC]; simp)
  have hreach : (G.nabla d).Reachable z0 z1 :=
    SimpleGraph.ConnectedComponent.exact (hz0.trans hz1.symm)
  have key := reachable_induction
    (fun x : G.fiber d => (G.nabla d).connectedComponentMk x = C ∧ 0 < x.1 i)
    (by
      rintro x y ⟨hxC, hxi⟩ hadj
      have hyC : (G.nabla d).connectedComponentMk y = C :=
        (SimpleGraph.ConnectedComponent.sound hadj.reachable).symm.trans hxC
      refine ⟨hyC, ?_⟩
      obtain ⟨-, k, hxk, hyk⟩ := hadj
      have hk : k ∈ G.compSupp C := hxC ▸ G.supp_subset_compSupp x (mem_supp.2 hxk)
      rw [hC, mem_insert, mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hyk
      · have := H x hxC hxi; omega)
    hreach ⟨hz0, hz0i⟩
  have := H z1 hz1 key.2
  omega
end SemigroupBetti.GenData
