-- Prove2me | solution 1 for SemigroupBetti.GenData.sigma_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:12:46.796395+00:00
-- url     : https://prove2.me/submissions/78bf6913-6f82-4e4f-8199-cfcc6ecec61e

module
public import Definitions.Def_SemigroupBetti_Fiber
public import Definitions.Def_SemigroupBetti_Critical
public import Theorems.Thm_SemigroupBetti_GenData_mem_singletonDegrees
public import Theorems.Thm_SemigroupBetti_GenData_ncomp_sub_one_le
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
theorem _root_.solution : G.sigma ≤ 4 := by
  classical
  let f : Fin 4 → ℕ := fun i => G.crit i * G.n i
  let s := univ.filter (fun i => f i ∈ G.singletonDegrees)
  have hmaps : (s : Set (Fin 4)).MapsTo f G.singletonDegrees := fun i hi => (mem_filter.1 hi).2
  calc G.sigma = ∑ d ∈ G.singletonDegrees, (G.ncomp d - 1) := rfl
    _ ≤ ∑ d ∈ G.singletonDegrees, (G.critIndices d).card := by
      apply sum_le_sum
      intro d hd
      obtain ⟨-, hc, hS⟩ := G.mem_singletonDegrees.1 hd
      exact G.ncomp_sub_one_le hc hS
    _ = ∑ d ∈ G.singletonDegrees, (s.filter (fun i => f i = d)).card := by
      apply sum_congr rfl
      intro d hd
      congr 1
      ext i
      simp only [critIndices, s, f, mem_filter, mem_univ, true_and]
      constructor
      · intro h; exact ⟨h ▸ hd, h⟩
      · exact fun h => h.2
    _ = s.card := (card_eq_sum_card_fiberwise hmaps).symm
    _ ≤ 4 := by simpa using card_le_univ s
end SemigroupBetti.GenData
