-- Prove2me | solution 1 for TreewidthApprox.Pushed.pushed_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:25:14.4617+00:00
-- url     : https://prove2.me/submissions/453267c1-3391-42a2-93aa-591d5f201ef8

import Mathlib
import Definitions.Def_TreewidthApprox_Pushed_Setting

set_option autoImplicit false
open TreewidthApprox.Pushed

theorem p3_iff {V : Type} [DecidableEq V] {W P Q R : Finset V} :
    IsPartition3 W P Q R ↔ ∀ v, ((v ∈ P ∨ v ∈ Q ∨ v ∈ R) ↔ v ∈ W) ∧ ¬ (v ∈ P ∧ v ∈ Q) ∧
      ¬ (v ∈ P ∧ v ∈ R) ∧ ¬ (v ∈ Q ∧ v ∈ R) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩ v
    refine ⟨?_, fun h => Finset.disjoint_left.mp h1 h.1 h.2,
      fun h => Finset.disjoint_left.mp h2 h.1 h.2, fun h => Finset.disjoint_left.mp h3 h.1 h.2⟩
    rw [← h4]; simp only [Finset.mem_union]; tauto
  · intro h
    refine ⟨Finset.disjoint_left.mpr fun v hv hv' => (h v).2.1 ⟨hv, hv'⟩,
      Finset.disjoint_left.mpr fun v hv hv' => (h v).2.2.1 ⟨hv, hv'⟩,
      Finset.disjoint_left.mpr fun v hv hv' => (h v).2.2.2 ⟨hv, hv'⟩, ?_⟩
    ext v; simp only [Finset.mem_union]; rw [or_assoc]; exact (h v).1

theorem restr_side {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hAB : Disjoint A B)
    (L X R : Finset V) (hLXR : IsSeparation G L X R) :
    IsTerminalSep G (A ∪ (B \ (X ∩ B))) (L ∩ B) (R ∩ B) (X ∩ A).card
        (L ∩ (A ∪ B)) (X ∩ A) (R ∩ (A ∪ B)) := by
  refine ⟨?_, ?_, ?_, ?_, le_refl _⟩
  · rw [p3_iff]
    intro v
    have hL := (p3_iff.mp hLXR.1) v
    have hd : v ∈ A → v ∉ B := fun h => Finset.disjoint_left.mp hAB h
    simp only [Finset.mem_univ, iff_true] at hL
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff]
    tauto
  · intro v hv
    simp only [Finset.mem_inter, Finset.mem_union] at hv ⊢
    tauto
  · intro v hv
    simp only [Finset.mem_inter, Finset.mem_union] at hv ⊢
    tauto
  · intro a ha b hb
    simp only [Finset.mem_inter] at ha hb
    exact hLXR.2 a ha.1 b hb.1

theorem side_card {V : Type} [DecidableEq V] (A B XB T T' L' : Finset V)
    (hAB : Disjoint A B) (hTB : T ⊆ B) (hBc : ∀ v, v ∈ B → v ∉ XB → v ∈ T ∨ v ∈ T')
    (hL' : L' ⊆ A ∪ (B \ XB)) (hT : T ⊆ L') (hT' : Disjoint T' L') :
    L'.card = (L' ∩ A).card + T.card := by
  have e : L' = (L' ∩ A) ∪ T := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hv
      have h1 := hL' hv
      simp only [Finset.mem_union, Finset.mem_sdiff] at h1
      rcases h1 with h1 | ⟨h1, h2⟩
      · exact Or.inl ⟨hv, h1⟩
      · rcases hBc v h1 h2 with h3 | h3
        · exact Or.inr h3
        · exact absurd hv (Finset.disjoint_left.mp hT' h3)
    · rintro (⟨h, _⟩ | h)
      · exact h
      · exact hT h
  have d : Disjoint (L' ∩ A) T := by
    refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
    exact Finset.disjoint_left.mp hAB (Finset.mem_inter.mp h1).2 (hTB h2)
  have h := congrArg Finset.card e
  rw [Finset.card_union_of_disjoint d] at h
  exact h

theorem left_ge {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hAB : Disjoint A B)
    (L X R : Finset V) (hLXR : IsSeparation G L X R)
    (L₁ X₁ R₁ : Finset V)
    (h : IsLeftPushed G (A ∪ (B \ (X ∩ B))) (L ∩ B) (R ∩ B) (X ∩ A).card L₁ X₁ R₁) :
    (L ∩ A).card ≤ (L₁ ∩ A).card := by
  have hRes := restr_side G A B hAB L X R hLXR
  have hmax := h.2 _ _ _ hRes
  have hp := p3_iff.mp hLXR.1
  have hB : ∀ v, v ∈ B → v ∉ X ∩ B → v ∈ L ∩ B ∨ v ∈ R ∩ B := by
    intro v h1 h2
    have := (hp v).1.mpr (Finset.mem_univ v)
    simp only [Finset.mem_inter] at h2 ⊢
    tauto
  have hp1 := p3_iff.mp h.1.1
  have c1 : L₁.card = (L₁ ∩ A).card + (L ∩ B).card := by
    refine side_card A B (X ∩ B) (L ∩ B) (R ∩ B) L₁ hAB Finset.inter_subset_right hB ?_
      h.1.2.1 ?_
    · intro v hv; exact ((hp1 v).1.mp (Or.inl hv))
    · refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
      exact (hp1 v).2.2.1 ⟨h2, h.1.2.2.1 h1⟩
  have hL2 : L ∩ (A ∪ B) ⊆ A ∪ (B \ (X ∩ B)) := by
    intro v hv
    have := (hp v)
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at hv ⊢
    tauto
  have c2 : (L ∩ (A ∪ B)).card = ((L ∩ (A ∪ B)) ∩ A).card + (L ∩ B).card := by
    refine side_card A B (X ∩ B) (L ∩ B) (R ∩ B) (L ∩ (A ∪ B)) hAB Finset.inter_subset_right hB
      hL2 ?_ ?_
    · intro v hv
      simp only [Finset.mem_inter, Finset.mem_union] at hv ⊢
      tauto
    · refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
      simp only [Finset.mem_inter, Finset.mem_union] at h1 h2
      exact (hp v).2.2.1 ⟨h2.1, h1.1⟩
  have e : (L ∩ (A ∪ B)) ∩ A = L ∩ A := by
    ext v; simp only [Finset.mem_inter, Finset.mem_union]; tauto
  rw [e] at c2
  omega

theorem right_ge {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hAB : Disjoint A B)
    (L X R : Finset V) (hLXR : IsSeparation G L X R)
    (L₁ X₁ R₁ : Finset V)
    (h : IsRightPushed G (A ∪ (B \ (X ∩ B))) (L ∩ B) (R ∩ B) (X ∩ A).card L₁ X₁ R₁) :
    (R ∩ A).card ≤ (R₁ ∩ A).card := by
  have hRes := restr_side G A B hAB L X R hLXR
  have hmax := h.2 _ _ _ hRes
  have hp := p3_iff.mp hLXR.1
  have hB : ∀ v, v ∈ B → v ∉ X ∩ B → v ∈ R ∩ B ∨ v ∈ L ∩ B := by
    intro v h1 h2
    have := (hp v).1.mpr (Finset.mem_univ v)
    simp only [Finset.mem_inter] at h2 ⊢
    tauto
  have hp1 := p3_iff.mp h.1.1
  have c1 : R₁.card = (R₁ ∩ A).card + (R ∩ B).card := by
    refine side_card A B (X ∩ B) (R ∩ B) (L ∩ B) R₁ hAB Finset.inter_subset_right hB ?_
      h.1.2.2.1 ?_
    · intro v hv; exact ((hp1 v).1.mp (Or.inr (Or.inr hv)))
    · refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
      exact (hp1 v).2.2.1 ⟨h.1.2.1 h1, h2⟩
  have hL2 : R ∩ (A ∪ B) ⊆ A ∪ (B \ (X ∩ B)) := by
    intro v hv
    have := (hp v)
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff] at hv ⊢
    tauto
  have c2 : (R ∩ (A ∪ B)).card = ((R ∩ (A ∪ B)) ∩ A).card + (R ∩ B).card := by
    refine side_card A B (X ∩ B) (R ∩ B) (L ∩ B) (R ∩ (A ∪ B)) hAB Finset.inter_subset_right hB
      hL2 ?_ ?_
    · intro v hv
      simp only [Finset.mem_inter, Finset.mem_union] at hv ⊢
      tauto
    · refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
      simp only [Finset.mem_inter, Finset.mem_union] at h1 h2
      exact (hp v).2.2.1 ⟨h1.1, h2.1⟩
  have e : (R ∩ (A ∪ B)) ∩ A = R ∩ A := by
    ext v; simp only [Finset.mem_inter, Finset.mem_union]; tauto
  rw [e] at c2
  omega

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A₁ B A₂ : Finset V) (hAB : IsSeparation G A₁ B A₂)
    (L X R : Finset V) (hLXR : IsSeparation G L X R) :
    (∀ L₁ X₁ R₁ : Finset V,
        IsLeftPushed G (A₁ ∪ (B \ (X ∩ B))) (L ∩ B) (R ∩ B) (X ∩ A₁).card L₁ X₁ R₁ →
        (L ∩ A₁).card ≤ (L₁ ∩ A₁).card) ∧
      (∀ L₂ X₂ R₂ : Finset V,
        IsRightPushed G (A₂ ∪ (B \ (X ∩ B))) (L ∩ B) (R ∩ B) (X ∩ A₂).card L₂ X₂ R₂ →
        (R ∩ A₂).card ≤ (R₂ ∩ A₂).card) := by
  have hp := p3_iff.mp hAB.1
  refine ⟨fun L₁ X₁ R₁ h => left_ge G A₁ B ?_ L X R hLXR L₁ X₁ R₁ h,
    fun L₂ X₂ R₂ h => right_ge G A₂ B ?_ L X R hLXR L₂ X₂ R₂ h⟩
  · refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
    have := hp v
    tauto
  · refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
    have := hp v
    tauto
