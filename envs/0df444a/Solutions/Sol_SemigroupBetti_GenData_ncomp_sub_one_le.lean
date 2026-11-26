-- Prove2me | solution 1 for SemigroupBetti.GenData.ncomp_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:11:39.042485+00:00
-- url     : https://prove2.me/submissions/0f781d42-8546-4629-ae60-959e979bdf86

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
public import Theorems.Thm_SemigroupBetti_GenData_degree_eq_of_singleton_comp
public import Theorems.Thm_SemigroupBetti_GenData_compSupp_disjoint
public import Theorems.Thm_SemigroupBetti_GenData_compSupp_nonempty
public import Theorems.Thm_SemigroupBetti_GenData_mem_fiber
public import Theorems.Thm_SemigroupBetti_GenData_n_one
public import Theorems.Thm_SemigroupBetti_GenData_n_three
public import Theorems.Thm_SemigroupBetti_GenData_n_two
public import Theorems.Thm_SemigroupBetti_GenData_n_zero
public import Theorems.Thm_SemigroupBetti_GenData_nu_zero
public import Theorems.Thm_SemigroupBetti_GenData_pos_of_two_le_ncomp
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
theorem _root_.solution {d : ℕ} (hd : G.contributes d) (hS : G.HasSingletonComp d) :
    G.ncomp d - 1 ≤ (G.critIndices d).card := by
  classical
  have hdpos := G.pos_of_two_le_ncomp hd
  set K1 := (univ : Finset (G.nabla d).ConnectedComponent).filter
    (fun C => (G.compSupp C).card = 1) with hK1
  set K2 := (univ : Finset (G.nabla d).ConnectedComponent).filter
    (fun C => ¬ (G.compSupp C).card = 1) with hK2
  have hsplit : K1.card + K2.card = G.ncomp d := by
    rw [hK1, hK2, card_filter_add_card_filter_not]; rfl
  -- `r_d = #K1 ≤ #{i : cᵢ nᵢ = d}`: the singleton supports are disjoint and indexed by
  -- critical indices (Lemmas 2.1 and 3.4)
  have hK1le : K1.card ≤ (G.critIndices d).card := by
    have hdisj : (K1 : Set (G.nabla d).ConnectedComponent).PairwiseDisjoint G.compSupp :=
      fun C _ C' _ h => G.compSupp_disjoint h
    have hcard : (K1.biUnion G.compSupp).card = K1.card := by
      rw [card_biUnion hdisj]
      rw [Finset.sum_congr rfl (fun C hC => (mem_filter.1 hC).2)]
      simp [hK1]
    rw [← hcard]
    apply card_le_card
    intro i hi
    obtain ⟨C, hC, hiC⟩ := mem_biUnion.1 hi
    obtain ⟨i', hi'⟩ := card_eq_one.1 (mem_filter.1 hC).2
    rw [hi', mem_singleton] at hiC
    subst hiC
    simp only [critIndices, mem_filter, mem_univ, true_and]
    exact (G.degree_eq_of_singleton_comp hd hi').symm
  -- at most one component with support of size `≥ 2`
  have hK2le : K2.card ≤ 1 := by
    obtain ⟨C0, hC0⟩ := hS
    rw [card_le_one]
    intro C hC C' hC'
    by_contra hne
    have hC2 : 2 ≤ (G.compSupp C).card := by
      have h1 := (mem_filter.1 hC).2
      have h0 := (G.compSupp_nonempty hdpos C).card_pos
      omega
    have hC'2 : 2 ≤ (G.compSupp C').card := by
      have h1 := (mem_filter.1 hC').2
      have h0 := (G.compSupp_nonempty hdpos C').card_pos
      omega
    have hCC0 : C ≠ C0 := by rintro rfl; exact (mem_filter.1 hC).2 hC0
    have hC'C0 : C' ≠ C0 := by rintro rfl; exact (mem_filter.1 hC').2 hC0
    have hu := card_le_univ (G.compSupp C ∪ G.compSupp C' ∪ G.compSupp C0)
    rw [card_union_of_disjoint, card_union_of_disjoint (G.compSupp_disjoint hne)] at hu
    · simp only [Fintype.card_fin] at hu; omega
    · exact disjoint_union_left.2 ⟨G.compSupp_disjoint hCC0, G.compSupp_disjoint hC'C0⟩
  omega
end SemigroupBetti.GenData
