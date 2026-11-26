-- Prove2me | solution 1 for SemigroupBetti.GenData.rep_sub_rep_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:07:49.195806+00:00
-- url     : https://prove2.me/submissions/0e29ca3b-f792-4f8d-859d-ade5a938ede5

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Bridge
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
theorem _root_.solution {d : ℕ} (hd : d ≤ G.H) (C C' : (G.nabla d).ConnectedComponent) :
    mono K (G.rep C) - mono K (G.rep C') ∈ Ideal.span (G.binomGens K : Set _) := by
  classical
  have h : Nonempty (G.nabla d).ConnectedComponent := ⟨C⟩
  have base : ∀ D : (G.nabla d).ConnectedComponent, mono K (G.rep D) - mono K (G.rep (Classical.choice h)) ∈
      Ideal.span (G.binomGens K : Set _) := by
    intro D
    by_cases hD : D = Classical.choice h
    · rw [hD, sub_self]; exact zero_mem _
    · apply Ideal.subset_span
      simp only [binomGens, coe_biUnion, coe_range, Set.mem_iUnion, mem_coe, Set.mem_Iio]
      refine ⟨d, by omega, ?_⟩
      unfold genSet
      simp only [h, ↓reduceDIte]
      exact mem_image.2 ⟨D, mem_erase.2 ⟨hD, mem_univ _⟩, rfl⟩
  rw [← sub_sub_sub_cancel_right _ _ (mono K (G.rep (Classical.choice h)))]
  exact sub_mem (base C) (base C')
end SemigroupBetti.GenData
