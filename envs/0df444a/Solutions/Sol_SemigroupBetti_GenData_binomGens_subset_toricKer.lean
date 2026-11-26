-- Prove2me | solution 1 for SemigroupBetti.GenData.binomGens_subset_toricKer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:09:38.948485+00:00
-- url     : https://prove2.me/submissions/65b89bb3-1964-49ef-ab5c-17100c6b5b29

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
public import Theorems.Thm_SemigroupBetti_GenData_mono_sub_mem_toricKer
public import Theorems.Thm_SemigroupBetti_GenData_nu_rep
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
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
open Finset MvPolynomial
open SemigroupBetti.GenData
variable (G : GenData) (K : Type*) [Field K]
namespace SemigroupBetti.GenData
theorem _root_.solution : (G.binomGens K : Set (MvPolynomial (Fin 4) K)) ⊆ G.toricKer K := by
  classical
  intro p hp
  simp only [binomGens, coe_biUnion, coe_range, Set.mem_iUnion, mem_coe] at hp
  obtain ⟨d, -, hp⟩ := hp
  unfold genSet at hp
  split_ifs at hp with h
  · obtain ⟨C, -, rfl⟩ := mem_image.1 hp
    apply G.mono_sub_mem_toricKer
    rw [G.nu_rep, G.nu_rep]
  · simp at hp
end SemigroupBetti.GenData
