-- Prove2me | solution 1 for TheoryOfGames.Decomposition.minimal_disjoint_or_subset
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T11:50:43.222996+00:00
-- url     : https://prove2.me/submissions/02152276-06e9-4816-a9e9-60ebb132a172

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

open TheoryOfGames.Decomposition in
theorem p274eda32_splitting_inter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (J₁ J₂ : Finset ι)
    (h₁ : IsSplitting v J₁) (h₂ : IsSplitting v J₂) : IsSplitting v (J₁ ∩ J₂) := by
  intro S T hS hT
  have hSJ1 : S ⊆ J₁ := hS.trans Finset.inter_subset_left
  have hSJ2 : S ⊆ J₂ := hS.trans Finset.inter_subset_right
  -- T = (T ∩ J₁) ∪ (T \ J₁)
  have hA1 : T ∩ J₁ ⊆ J₁ := Finset.inter_subset_right
  have hA2 : T ∩ J₁ ⊆ J₂ᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    intro hx2
    have hxT := (Finset.mem_inter.mp hx).1
    have hx1 := (Finset.mem_inter.mp hx).2
    have := hT hxT
    rw [Finset.mem_compl] at this
    exact this (Finset.mem_inter.mpr ⟨hx1, hx2⟩)
  have hB : T \ J₁ ⊆ J₁ᶜ := by
    intro x hx
    rw [Finset.mem_compl]
    exact (Finset.mem_sdiff.mp hx).2
  have hT_eq : T = (T ∩ J₁) ∪ (T \ J₁) := by
    ext x; by_cases hx : x ∈ J₁ <;> simp [hx]
  have hST : S ∪ T = (S ∪ (T ∩ J₁)) ∪ (T \ J₁) := by
    conv_lhs => rw [hT_eq]
    rw [Finset.union_assoc]
  have e1 : v (S ∪ T) = v (S ∪ (T ∩ J₁)) + v (T \ J₁) := by
    rw [hST]
    exact h₁ _ _ (Finset.union_subset hSJ1 hA1) hB
  have e2 : v (S ∪ (T ∩ J₁)) = v S + v (T ∩ J₁) := h₂ _ _ hSJ2 hA2
  have e3 : v T = v (T ∩ J₁) + v (T \ J₁) := by
    conv_lhs => rw [hT_eq]
    exact h₁ _ _ hA1 hB
  rw [e1, e2, e3]
  ring

open TheoryOfGames.Decomposition in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (K : Finset ι) (hK : IsSplitting v K)
    (J : Finset ι) (hJ : IsMinimalSplitting v J) :
    Disjoint J K ∨ J ⊆ K := by
  by_cases hcon : (J ∩ K).Nonempty
  · right
    have hs := p274eda32_splitting_inter v J K hJ.1 hK
    have e1 := hJ.2.2 _ hs hcon Finset.inter_subset_left
    rw [← e1]
    exact Finset.inter_subset_right
  · left
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.not_nonempty_iff_eq_empty.mp hcon
