-- Prove2me | solution 1 for TheoryOfGames.Decomposition.minimal_cover
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:35:12.829798+00:00
-- url     : https://prove2.me/submissions/29a16169-7733-4be5-a6ee-106d658244d3

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

set_option autoImplicit false

open TheoryOfGames.Decomposition in
theorem P2M12a6a60a_splitting_inter {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (J₁ J₂ : Finset ι) (h₁ : IsSplitting v J₁) (h₂ : IsSplitting v J₂) :
    IsSplitting v (J₁ ∩ J₂) := by
  intro S T hS hT
  have hS1 : S ⊆ J₁ := hS.trans Finset.inter_subset_left
  have hS2 : S ⊆ J₂ := hS.trans Finset.inter_subset_right
  set T₁ := T ∩ J₁ with hT₁
  set T₂ := T ∩ J₁ᶜ with hT₂
  have hTsplit : T = T₁ ∪ T₂ := by
    ext x; by_cases hx : x ∈ J₁ <;> simp [T₁, T₂, hx]
  have hT1J1 : T₁ ⊆ J₁ := Finset.inter_subset_right
  have hT2J1 : T₂ ⊆ J₁ᶜ := Finset.inter_subset_right
  have hT1J2 : T₁ ⊆ J₂ᶜ := by
    intro x hx
    have hxT : x ∈ T := (Finset.mem_inter.mp hx).1
    have hxJ1 : x ∈ J₁ := (Finset.mem_inter.mp hx).2
    have := hT hxT
    simp only [Finset.mem_compl, Finset.mem_inter, not_and] at this ⊢
    exact this hxJ1
  have hST1 : S ∪ T₁ ⊆ J₁ := Finset.union_subset hS1 hT1J1
  have e1 : v (S ∪ T) = v (S ∪ T₁) + v T₂ := by
    rw [← h₁ (S ∪ T₁) T₂ hST1 hT2J1, hTsplit, Finset.union_assoc]
  have e2 : v (S ∪ T₁) = v S + v T₁ := h₂ S T₁ hS2 hT1J2
  have e3 : v T = v T₁ + v T₂ := by
    rw [← h₁ T₁ T₂ hT1J1 hT2J1, ← hTsplit]
  rw [e1, e2, e3]; ring

open TheoryOfGames.Decomposition in
theorem P2M12a6a60a_splitting_compl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (J : Finset ι) (h : IsSplitting v J) :
    IsSplitting v Jᶜ := by
  intro S T hS hT
  rw [compl_compl] at hT
  rw [Finset.union_comm, h T S hT hS, add_comm]

open TheoryOfGames.Decomposition in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (k : ι) :
    ∃ J : Finset ι, IsMinimalSplitting v J ∧ k ∈ J := by
  classical
  have huniv : IsSplitting v Finset.univ := by
    intro S T _ hT
    have hT0 : T = ∅ := by
      rw [Finset.compl_univ] at hT
      exact Finset.subset_empty.mp hT
    subst hT0
    rw [Finset.union_empty, hv.empty, add_zero]
  let P : Finset (Finset ι) :=
    (Finset.univ : Finset (Finset ι)).filter (fun J => IsSplitting v J ∧ k ∈ J)
  have hPne : P.Nonempty := ⟨Finset.univ, by simp [P, huniv]⟩
  obtain ⟨J, hJP, hJmin⟩ := Finset.exists_min_image P Finset.card hPne
  have hJ : IsSplitting v J ∧ k ∈ J := by simpa [P] using hJP
  refine ⟨J, ⟨hJ.1, ⟨k, hJ.2⟩, ?_⟩, hJ.2⟩
  intro J' hJ' hJ'ne hJ'sub
  by_cases hk : k ∈ J'
  · have hle := hJmin J' (by simp [P, hJ', hk])
    exact Finset.eq_of_subset_of_card_le hJ'sub hle
  · exfalso
    have hspl : IsSplitting v (J ∩ J'ᶜ) :=
      P2M12a6a60a_splitting_inter v J J'ᶜ hJ.1 (P2M12a6a60a_splitting_compl v J' hJ')
    have hkin : k ∈ J ∩ J'ᶜ := by simp [hJ.2, hk]
    have hle := hJmin (J ∩ J'ᶜ) (by simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hspl, hkin⟩)
    have heq : J ∩ J'ᶜ = J :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left hle
    obtain ⟨x, hx⟩ := hJ'ne
    have hxJ : x ∈ J := hJ'sub hx
    rw [← heq] at hxJ
    simp only [Finset.mem_inter, Finset.mem_compl] at hxJ
    exact hxJ.2 hx
