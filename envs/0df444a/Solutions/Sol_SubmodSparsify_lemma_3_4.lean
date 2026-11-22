-- Prove2me | solution 1 for SubmodSparsify.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @I am wealthy
-- created : 2026-11-21T17:03:20.906961+00:00
-- url     : https://prove2.me/submissions/7dbf14d7-f989-413c-b3bc-eecce786996f

import Definitions.Def_SubmodSparsify_blockMinCut
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
open SubmodSparsify NonmonotoneSubmod.Shared
namespace Submod1327
variable {α : Type} [Fintype α] [DecidableEq α]

theorem cut_le (f : Finset α → ℝ) {A B T : Finset α} (hA : A ⊆ T) (hB : Disjoint T B) :
    blockMinCut f A B ≤ f T := by
  let g := fun x : {T : Finset α // A ⊆ T ∧ Disjoint T B} => f x.val
  exact ciInf_le (Set.finite_range g).bddBelow (⟨T,hA,hB⟩ : {T : Finset α // A ⊆ T ∧ Disjoint T B})

theorem attained (f : Finset α → ℝ) {A B : Finset α} (h : Disjoint A B) :
    ∃ T, A ⊆ T ∧ Disjoint T B ∧ f T = blockMinCut f A B := by
  let I := {T : Finset α // A ⊆ T ∧ Disjoint T B}
  have : Nonempty I := ⟨⟨A, Finset.Subset.rfl,h⟩⟩
  obtain ⟨T,hT⟩ := exists_eq_ciInf_of_finite (f := fun T : I => f T.val)
  exact ⟨T.val,T.property.1,T.property.2,hT⟩

theorem mono_cut (f : Finset α → ℝ) {A A' B B' : Finset α}
    (ha : A ⊆ A') (hb : B ⊆ B') (hd : Disjoint A' B') :
    blockMinCut f A B ≤ blockMinCut f A' B' := by
  obtain ⟨T,hT,hdT,he⟩ := attained f hd
  rw [← he]
  exact cut_le f (ha.trans hT) (hdT.mono_right hb)


end Submod1327


noncomputable section
namespace Submod1327
open SubmodSparsify NonmonotoneSubmod.Shared
variable {α : Type} [Fintype α] [DecidableEq α]

lemma subset_of_disjoint_compl {X S : Finset α} (h : Disjoint X Sᶜ) : X ⊆ S := by
  intro a ha
  by_contra hs
  exact Finset.disjoint_left.mp h ha (Finset.mem_compl.mpr hs)

lemma residual_two_cuts (f : Finset α → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (S T : Finset α) :
    f S - f T ≤ blockMinCut f (S \ T) Sᶜ + blockMinCut f (S ∩ T) (T \ S) := by
  obtain ⟨X,hXA,hXB,hX⟩ := attained f (A := S \ T) (B := Sᶜ)
    (Finset.disjoint_left.mpr (by intro a ha hb; exact Finset.mem_compl.mp hb (Finset.mem_sdiff.mp ha).1))
  obtain ⟨Y,hYA,hYB,hY⟩ := attained f (A := S ∩ T) (B := T \ S)
    (Finset.disjoint_left.mpr (by intro a ha hb; exact (Finset.mem_sdiff.mp hb).2 (Finset.mem_inter.mp ha).1))
  have hXS := subset_of_disjoint_compl hXB
  have hU : X ∪ (S ∩ T) = S := by
    apply Finset.Subset.antisymm (Finset.union_subset hXS Finset.inter_subset_left)
    intro a ha
    by_cases ht : a ∈ T
    · exact Finset.mem_union_right X (Finset.mem_inter.mpr ⟨ha,ht⟩)
    · exact Finset.mem_union_left _ (hXA (Finset.mem_sdiff.mpr ⟨ha,ht⟩))
  have hI : Y ∩ T = S ∩ T := by
    apply Finset.Subset.antisymm
    · intro a ha
      obtain ⟨hy,ht⟩ := Finset.mem_inter.mp ha
      have hs : a ∈ S := by
        by_contra hs
        exact Finset.disjoint_left.mp hYB hy (Finset.mem_sdiff.mpr ⟨ht,hs⟩)
      exact Finset.mem_inter.mpr ⟨hs,ht⟩
    · intro a ha
      exact Finset.mem_inter.mpr ⟨hYA ha,(Finset.mem_inter.mp ha).2⟩
  have h1 := hf X (S ∩ T)
  have h2 := hf Y T
  rw [hU] at h1
  rw [hI] at h2
  linarith [hf0 (X ∩ (S ∩ T)), hf0 (Y ∪ T)]

lemma residual_bounds (f : Finset α → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hf : Submodular f) (S U : Finset α) :
    0 ≤ f S - blockMinCut f (S \ U) (Sᶜ \ U) ∧
      f S - blockMinCut f (S \ U) (Sᶜ \ U) ≤
        blockMinCut f (S ∩ U) Sᶜ + blockMinCut f S (U \ S) := by
  have hd : Disjoint (S \ U) (Sᶜ \ U) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact Finset.mem_compl.mp (Finset.mem_sdiff.mp hb).1 (Finset.mem_sdiff.mp ha).1
  have hSfeas : Disjoint S (Sᶜ \ U) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact Finset.mem_compl.mp (Finset.mem_sdiff.mp hb).1 ha
  constructor
  · exact sub_nonneg.mpr (cut_le f Finset.sdiff_subset hSfeas)
  · obtain ⟨Z,hZA,hZB,hZ⟩ := attained f hd
    have hA : S \ Z ⊆ S ∩ U := by
      intro a ha
      obtain ⟨hs,hz⟩ := Finset.mem_sdiff.mp ha
      refine Finset.mem_inter.mpr ⟨hs,?_⟩
      by_contra hu
      exact hz (hZA (Finset.mem_sdiff.mpr ⟨hs,hu⟩))
    have hB : Z \ S ⊆ U \ S := by
      intro a ha
      obtain ⟨hz,hs⟩ := Finset.mem_sdiff.mp ha
      refine Finset.mem_sdiff.mpr ⟨?_,hs⟩
      by_contra hu
      exact Finset.disjoint_left.mp hZB hz
        (Finset.mem_sdiff.mpr ⟨Finset.mem_compl.mpr hs,hu⟩)
    have hfirst := residual_two_cuts f hf0 hf S Z
    have hm1 := mono_cut f hA ((Finset.Subset.rfl : Sᶜ ⊆ Sᶜ))
      (Finset.disjoint_left.mpr (by intro a ha hb; exact Finset.mem_compl.mp hb (Finset.mem_inter.mp ha).1))
    have hm2 := mono_cut f (Finset.inter_subset_left : S ∩ Z ⊆ S) hB
      (Finset.disjoint_left.mpr (by intro a ha hb; exact (Finset.mem_sdiff.mp hb).2 ha))
    rw [hZ] at hfirst
    linarith

lemma residual_monotone (f : Finset α → ℝ) (S U U' : Finset α) (hU : U ⊆ U') :
    f S - blockMinCut f (S \ U) (Sᶜ \ U) ≤
      f S - blockMinCut f (S \ U') (Sᶜ \ U') := by
  have hA : S \ U' ⊆ S \ U := by
    intro a ha
    obtain ⟨hs,hu⟩ := Finset.mem_sdiff.mp ha
    exact Finset.mem_sdiff.mpr ⟨hs,fun h => hu (hU h)⟩
  have hB : Sᶜ \ U' ⊆ Sᶜ \ U := by
    intro a ha
    obtain ⟨hs,hu⟩ := Finset.mem_sdiff.mp ha
    exact Finset.mem_sdiff.mpr ⟨hs,fun h => hu (hU h)⟩
  have hd : Disjoint (S \ U) (Sᶜ \ U) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact Finset.mem_compl.mp (Finset.mem_sdiff.mp hb).1 (Finset.mem_sdiff.mp ha).1
  linarith [mono_cut f hA hB hd]

lemma residual_endpoints (f : Finset α → ℝ) (hf0 : ∀ S, 0 ≤ f S)
    (hempty : f ∅ = 0) (S : Finset α) :
    f S - blockMinCut f (S \ ∅) (Sᶜ \ ∅) = 0 ∧
      f S - blockMinCut f (S \ Finset.univ) (Sᶜ \ Finset.univ) = f S := by
  have hfull : blockMinCut f S Sᶜ = f S := by
    obtain ⟨T,hTS,hTB,hT⟩ := attained f (disjoint_compl_right : Disjoint S Sᶜ)
    have he : T = S := Finset.Subset.antisymm (subset_of_disjoint_compl hTB) hTS
    simpa [he] using hT.symm
  have hnone : blockMinCut f ∅ ∅ = 0 := by
    obtain ⟨T,hTA,hTB,hT⟩ := attained f (show Disjoint (∅ : Finset α) ∅ by simp)
    have hl : 0 ≤ blockMinCut f ∅ ∅ := by rw [← hT]; exact hf0 T
    have hu : blockMinCut f ∅ ∅ ≤ 0 := by
      rw [← hempty]
      exact cut_le f (Finset.empty_subset ∅) (by simp)
    exact le_antisymm hu hl
  have hs : S \ Finset.univ = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ S)
  have hsc : Sᶜ \ Finset.univ = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ Sᶜ)
  simp only [Finset.sdiff_empty, hs, hsc, hfull, hnone, sub_self, sub_zero, and_self]

end Submod1327

open SubmodSparsify
set_option autoImplicit false

theorem solution {α : Type} [Fintype α] [DecidableEq α] (f : Finset α → ℝ)
    (hf0 : ∀ S, 0 ≤ f S) (hf : NonmonotoneSubmod.Shared.Submodular f)
    (hempty : f ∅ = 0) (huniv : f Finset.univ = 0) :
    (∀ S T : Finset α,
      f S - f T ≤ blockMinCut f (S \ T) Sᶜ + blockMinCut f (S ∩ T) (T \ S)) ∧
    (∀ S U : Finset α, 0 ≤ f S - blockMinCut f (S \ U) (Sᶜ \ U) ∧
      f S - blockMinCut f (S \ U) (Sᶜ \ U) ≤
        blockMinCut f (S ∩ U) Sᶜ + blockMinCut f S (U \ S)) ∧
    (∀ S U U' : Finset α, U ⊆ U' →
      f S - blockMinCut f (S \ U) (Sᶜ \ U) ≤ f S - blockMinCut f (S \ U') (Sᶜ \ U')) ∧
    (∀ S : Finset α, f S - blockMinCut f (S \ ∅) (Sᶜ \ ∅) = 0 ∧
      f S - blockMinCut f (S \ Finset.univ) (Sᶜ \ Finset.univ) = f S)  := by
  exact ⟨Submod1327.residual_two_cuts f hf0 hf,
    Submod1327.residual_bounds f hf0 hf,
    Submod1327.residual_monotone f,
    Submod1327.residual_endpoints f hf0 hempty⟩

