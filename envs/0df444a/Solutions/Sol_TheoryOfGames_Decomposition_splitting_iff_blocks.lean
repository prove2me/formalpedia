-- Prove2me | solution 1 for TheoryOfGames.Decomposition.splitting_iff_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T14:39:52.391585+00:00
-- url     : https://prove2.me/submissions/91f06dcc-aae4-4665-8fc6-78edbcc8d1ca

import Mathlib
import Definitions.Def_TheoryOfGames_Decomposition_IsConstantSum
import Definitions.Def_TheoryOfGames_Decomposition_Splitting

set_option autoImplicit false

namespace P8607813d
open TheoryOfGames.Decomposition

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma split_compl (v : Finset ι → ℝ) (J : Finset ι) (h : IsSplitting v J) :
    IsSplitting v Jᶜ := by
  intro S T hS hT
  rw [compl_compl] at hT
  rw [Finset.union_comm, h T S hT hS, add_comm]

lemma split_inter (v : Finset ι → ℝ) (J1 J2 : Finset ι) (h1 : IsSplitting v J1)
    (h2 : IsSplitting v J2) : IsSplitting v (J1 ∩ J2) := by
  intro S T hS hT
  have hT2a : T ∩ J1 ⊆ J1 := Finset.inter_subset_right
  have hT2b : T ∩ J1 ⊆ J2ᶜ := by
    intro x hx
    have hxT := (Finset.mem_inter.1 hx).1
    have hxJ1 := (Finset.mem_inter.1 hx).2
    have := hT hxT
    simp only [Finset.mem_compl, Finset.mem_inter, not_and] at this ⊢
    exact this hxJ1
  have hT1 : T ∩ J1ᶜ ⊆ J1ᶜ := Finset.inter_subset_right
  have hTeq : T = (T ∩ J1) ∪ (T ∩ J1ᶜ) := by
    ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_compl]; tauto
  have hSJ1 : S ⊆ J1 := hS.trans Finset.inter_subset_left
  have hSJ2 : S ⊆ J2 := hS.trans Finset.inter_subset_right
  have e1 : v (S ∪ T) = v (S ∪ (T ∩ J1)) + v (T ∩ J1ᶜ) := by
    have := h1 (S ∪ (T ∩ J1)) (T ∩ J1ᶜ) (Finset.union_subset hSJ1 hT2a) hT1
    rw [Finset.union_assoc, ← hTeq] at this
    exact this
  have e2 : v (S ∪ (T ∩ J1)) = v S + v (T ∩ J1) := h2 S (T ∩ J1) hSJ2 hT2b
  have e3 : v T = v (T ∩ J1) + v (T ∩ J1ᶜ) := by
    have := h1 (T ∩ J1) (T ∩ J1ᶜ) hT2a hT1
    rwa [← hTeq] at this
  rw [e1, e2, e3]; ring

lemma split_union (v : Finset ι → ℝ) (J1 J2 : Finset ι) (h1 : IsSplitting v J1)
    (h2 : IsSplitting v J2) : IsSplitting v (J1 ∪ J2) := by
  have := split_compl v _ (split_inter v _ _ (split_compl v _ h1) (split_compl v _ h2))
  rwa [← Finset.compl_union, compl_compl] at this

lemma split_empty (v : Finset ι → ℝ) (hv : v ∅ = 0) : IsSplitting v ∅ := by
  intro S T hS _
  have : S = ∅ := Finset.subset_empty.1 hS
  subst this; simp [hv]

lemma split_univ (v : Finset ι → ℝ) (hv : v ∅ = 0) : IsSplitting v Finset.univ := by
  intro S T _ hT
  have : T = ∅ := Finset.subset_empty.1 (by simpa using hT)
  subst this; simp [hv]

lemma exists_min (v : Finset ι → ℝ) (hv : v ∅ = 0) (i : ι) :
    ∃ M, IsMinimalSplitting v M ∧ i ∈ M := by
  classical
  have hne : (Finset.univ.filter (fun J : Finset ι => IsSplitting v J ∧ i ∈ J)).Nonempty :=
    ⟨Finset.univ, by simp [split_univ v hv]⟩
  obtain ⟨M, hM, hmin⟩ := Finset.exists_min_image _ Finset.card hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hM hmin
  refine ⟨M, ⟨hM.1, ⟨i, hM.2⟩, ?_⟩, hM.2⟩
  intro J' hJ' hne' hsub
  by_cases hi : i ∈ J'
  · exact Finset.eq_of_subset_of_card_le hsub (hmin J' ⟨hJ', hi⟩)
  · exfalso
    have hs : IsSplitting v (M ∩ J'ᶜ) := split_inter v _ _ hM.1 (split_compl v _ hJ')
    have hc := hmin _ ⟨hs, by simp [hM.2, hi]⟩
    have hlt : (M ∩ J'ᶜ).card < M.card := by
      apply Finset.card_lt_card
      refine ⟨Finset.inter_subset_left, ?_⟩
      intro h
      obtain ⟨x, hx⟩ := hne'
      have := (Finset.mem_inter.1 (h (hsub hx))).2
      exact (Finset.mem_compl.1 this) hx
    omega

end P8607813d

open TheoryOfGames.Decomposition in
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : Finset ι → ℝ) (hv : IsConstantSum v) (K : Finset ι) :
    IsSplitting v K ↔ ∀ J ∈ decompositionPartition v, J ⊆ K ∨ Disjoint J K := by
  constructor
  · intro hK J hJ
    obtain ⟨hJs, _, hJmin⟩ := hJ
    by_cases h : (J ∩ K).Nonempty
    · left
      have := hJmin _ (P8607813d.split_inter v _ _ hJs hK) h Finset.inter_subset_left
      rw [← this]; exact Finset.inter_subset_right
    · right
      rw [Finset.not_nonempty_iff_eq_empty] at h
      exact Finset.disjoint_iff_inter_eq_empty.2 h
  · intro h
    choose M hM hiM using P8607813d.exists_min v hv.empty
    have hsub : ∀ i ∈ K, M i ⊆ K := by
      intro i hi
      rcases h (M i) (hM i) with h1 | h1
      · exact h1
      · exact absurd hi (Finset.disjoint_left.1 h1 (hiM i))
    have hK : K = K.biUnion M := by
      ext x; simp only [Finset.mem_biUnion]
      constructor
      · intro hx; exact ⟨x, hx, hiM x⟩
      · rintro ⟨i, hi, hx⟩; exact hsub i hi hx
    have key : ∀ s : Finset ι, IsSplitting v (s.biUnion M) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simpa using P8607813d.split_empty v hv.empty
      · intro a s _ ih
        rw [Finset.biUnion_insert]
        exact P8607813d.split_union v _ _ (hM a).1 ih
    rw [hK]; exact key K
