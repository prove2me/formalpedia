-- Prove2me | solution 1 for TheoryOfGames.Decomposition.decomposition_partition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T17:18:07.966081+00:00
-- url     : https://prove2.me/submissions/83db1ea4-c00a-44d5-8a53-26073073de7c

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

set_option autoImplicit false

open TheoryOfGames.Decomposition in
theorem Pa4cb9a36_splitting_inter {ι : Type*} [Fintype ι] [DecidableEq ι]
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
theorem Pa4cb9a36_splitting_compl {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (J : Finset ι) (h : IsSplitting v J) :
    IsSplitting v Jᶜ := by
  intro S T hS hT
  rw [compl_compl] at hT
  rw [Finset.union_comm, h T S hT hS, add_comm]

open TheoryOfGames.Decomposition in
theorem Pa4cb9a36_splitting_union {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (J₁ J₂ : Finset ι) (h₁ : IsSplitting v J₁) (h₂ : IsSplitting v J₂) :
    IsSplitting v (J₁ ∪ J₂) := by
  have h := Pa4cb9a36_splitting_compl v _
    (Pa4cb9a36_splitting_inter v _ _ (Pa4cb9a36_splitting_compl v J₁ h₁)
      (Pa4cb9a36_splitting_compl v J₂ h₂))
  have e : (J₁ᶜ ∩ J₂ᶜ)ᶜ = J₁ ∪ J₂ := by
    rw [← Finset.compl_union, compl_compl]
  rwa [e] at h

open TheoryOfGames.Decomposition in
theorem Pa4cb9a36_splitting_empty {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) : IsSplitting v ∅ := by
  intro S T hS _
  have hS0 : S = ∅ := Finset.subset_empty.mp hS
  subst hS0
  rw [Finset.empty_union, hv.empty, zero_add]

open TheoryOfGames.Decomposition in
theorem Pa4cb9a36_splitting_sup {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (A : Finset (Finset ι))
    (hA : ∀ J ∈ A, IsSplitting v J) : IsSplitting v (A.sup id) := by
  induction A using Finset.induction_on with
  | empty => simpa using Pa4cb9a36_splitting_empty v hv
  | insert J A hJ ih =>
    rw [Finset.sup_insert]
    exact Pa4cb9a36_splitting_union v _ _ (hA J (Finset.mem_insert_self _ _))
      (ih (fun J' hJ' => hA J' (Finset.mem_insert_of_mem hJ')))

open TheoryOfGames.Decomposition in
theorem Pa4cb9a36_cover {ι : Type*} [Fintype ι] [DecidableEq ι]
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
      Pa4cb9a36_splitting_inter v J J'ᶜ hJ.1 (Pa4cb9a36_splitting_compl v J' hJ')
    have hkin : k ∈ J ∩ J'ᶜ := by simp [hJ.2, hk]
    have hle := hJmin (J ∩ J'ᶜ) (by simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hspl, hkin⟩)
    have heq : J ∩ J'ᶜ = J :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left hle
    obtain ⟨x, hx⟩ := hJ'ne
    have hxJ : x ∈ J := hJ'sub hx
    rw [← heq] at hxJ
    simp only [Finset.mem_inter, Finset.mem_compl] at hxJ
    exact hxJ.2 hx

open TheoryOfGames.Decomposition in
theorem Pa4cb9a36_disjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (J₁ J₂ : Finset ι)
    (h₁ : IsMinimalSplitting v J₁) (h₂ : IsMinimalSplitting v J₂) (hne : J₁ ≠ J₂) :
    Disjoint J₁ J₂ := by
  rw [Finset.disjoint_iff_inter_eq_empty]
  by_contra hcon
  have hnon : (J₁ ∩ J₂).Nonempty := Finset.nonempty_iff_ne_empty.mpr hcon
  have hs := Pa4cb9a36_splitting_inter v J₁ J₂ h₁.1 h₂.1
  have e1 := h₁.2.2 _ hs hnon Finset.inter_subset_left
  have e2 := h₂.2.2 _ hs hnon Finset.inter_subset_right
  exact hne (e1.symm.trans e2)

open TheoryOfGames.Decomposition in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) :
    (∀ J₁ ∈ decompositionPartition v, ∀ J₂ ∈ decompositionPartition v,
        J₁ ≠ J₂ → Disjoint J₁ J₂) ∧
      (∀ k : ι, ∃ J ∈ decompositionPartition v, k ∈ J) ∧
      (∀ K : Finset ι, IsSplitting v K ↔
        ∃ A : Finset (Finset ι), (∀ J ∈ A, J ∈ decompositionPartition v) ∧
          K = A.sup id) := by
  classical
  refine ⟨fun J₁ h₁ J₂ h₂ hne => Pa4cb9a36_disjoint v J₁ J₂ h₁ h₂ hne,
    fun k => Pa4cb9a36_cover v hv k, fun K => ⟨fun hK => ?_, fun ⟨A, hA, hKA⟩ => ?_⟩⟩
  · refine ⟨(Finset.univ : Finset (Finset ι)).filter (fun J => IsMinimalSplitting v J ∧ J ⊆ K),
      fun J hJ => (Finset.mem_filter.mp hJ).2.1, ?_⟩
    apply le_antisymm
    · intro k hk
      obtain ⟨J, hJ, hkJ⟩ := Pa4cb9a36_cover v hv k
      have hsub : J ⊆ K := by
        have hs := Pa4cb9a36_splitting_inter v J K hJ.1 hK
        have e := hJ.2.2 _ hs ⟨k, Finset.mem_inter.mpr ⟨hkJ, hk⟩⟩ Finset.inter_subset_left
        rw [← e]; exact Finset.inter_subset_right
      have hmem : J ∈ (Finset.univ : Finset (Finset ι)).filter
          (fun J => IsMinimalSplitting v J ∧ J ⊆ K) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hJ, hsub⟩
      exact (Finset.le_sup (f := id) hmem) hkJ
    · exact Finset.sup_le (fun J hJ => (Finset.mem_filter.mp hJ).2.2)
  · rw [hKA]
    exact Pa4cb9a36_splitting_sup v hv A (fun J hJ => (hA J hJ).1)
