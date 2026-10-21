-- Prove2me | solution 1 for TreewidthApprox.Pushed.glue_terminal_sep
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:20:15.614739+00:00
-- url     : https://prove2.me/submissions/c7279e6b-214f-43f1-b5c1-5171c8aa3e13

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


theorem glue_part (a1 b a2 tl xb tr l1 x1 r1 l2 x2 r2 : Prop)
    (hA : (a1 ∨ b ∨ a2) ∧ ¬(a1 ∧ b) ∧ ¬(a1 ∧ a2) ∧ ¬(b ∧ a2))
    (hB : ((tl ∨ xb ∨ tr) ↔ b) ∧ ¬(tl ∧ xb) ∧ ¬(tl ∧ tr) ∧ ¬(xb ∧ tr))
    (h1 : ((l1 ∨ x1 ∨ r1) ↔ a1 ∨ (b ∧ ¬ xb)) ∧ ¬(l1 ∧ x1) ∧ ¬(l1 ∧ r1) ∧ ¬(x1 ∧ r1))
    (h2 : ((l2 ∨ x2 ∨ r2) ↔ a2 ∨ (b ∧ ¬ xb)) ∧ ¬(l2 ∧ x2) ∧ ¬(l2 ∧ r2) ∧ ¬(x2 ∧ r2))
    (t1 : tl → l1) (t2 : tr → r1) (t3 : tl → l2) (t4 : tr → r2) :
    ((((l1 ∨ tl) ∨ l2) ∨ ((x1 ∨ xb) ∨ x2) ∨ ((r1 ∨ tr) ∨ r2))) ∧
      ¬(((l1 ∨ tl) ∨ l2) ∧ ((x1 ∨ xb) ∨ x2)) ∧
      ¬(((l1 ∨ tl) ∨ l2) ∧ ((r1 ∨ tr) ∨ r2)) ∧
      ¬(((x1 ∨ xb) ∨ x2) ∧ ((r1 ∨ tr) ∨ r2)) := by
  by_cases hb : b
  · have hna1 : ¬ a1 := fun h => hA.2.1 ⟨h, hb⟩
    have hna2 : ¬ a2 := fun h => hA.2.2.2 ⟨hb, h⟩
    rcases hB.1.mpr hb with htl | hxb | htr
    · have hl1 := t1 htl
      have hl2 := t3 htl
      have hnxb : ¬ xb := fun h => hB.2.1 ⟨htl, h⟩
      have hntr : ¬ tr := fun h => hB.2.2.1 ⟨htl, h⟩
      simp_all
    · have hntl : ¬ tl := fun h => hB.2.1 ⟨h, hxb⟩
      have hntr : ¬ tr := fun h => hB.2.2.2 ⟨hxb, h⟩
      simp_all
    · have hr1 := t2 htr
      have hr2 := t4 htr
      have hnxb : ¬ xb := fun h => hB.2.2.2 ⟨h, htr⟩
      have hntl : ¬ tl := fun h => hB.2.2.1 ⟨h, htr⟩
      simp_all
  · have hntl : ¬ tl := fun h => hb (hB.1.mp (Or.inl h))
    have hnxb : ¬ xb := fun h => hb (hB.1.mp (Or.inr (Or.inl h)))
    have hntr : ¬ tr := fun h => hb (hB.1.mp (Or.inr (Or.inr h)))
    rcases hA.1 with ha1 | hb' | ha2
    · have hna2 : ¬ a2 := fun h => hA.2.2.1 ⟨ha1, h⟩
      rcases h1.1.mpr (Or.inl ha1) with hl | hx | hr <;> simp_all
    · exact absurd hb' hb
    · have hna1 : ¬ a1 := fun h => hA.2.2.1 ⟨h, ha2⟩
      rcases h2.1.mpr (Or.inl ha2) with hl | hx | hr <;> simp_all

theorem glue_cls (a1 a2 b xb s1 s2 t t' o1 o2 : Prop)
    (ts1 : t → s1) (ts2 : t → s2) (to1 : t' → o1) (to2 : t' → o2)
    (hB : b ∧ ¬ xb → t ∨ t')
    (hs1 : s1 → a1 ∨ (b ∧ ¬ xb)) (hs2 : s2 → a2 ∨ (b ∧ ¬ xb))
    (ho1 : s1 → ¬ o1) (ho2 : s2 → ¬ o2) :
    ((s1 ∨ t) ∨ s2) → (a1 ∧ s1) ∨ (a2 ∧ s2) ∨ (s1 ∧ s2 ∧ t) := by
  intro h
  rcases h with (h | h) | h
  · rcases hs1 h with h' | h'
    · exact Or.inl ⟨h', h⟩
    · rcases hB h' with ht | ht'
      · exact Or.inr (Or.inr ⟨h, ts2 ht, ht⟩)
      · exact absurd (to1 ht') (ho1 h)
  · exact Or.inr (Or.inr ⟨ts1 h, ts2 h, h⟩)
  · rcases hs2 h with h' | h'
    · exact Or.inr (Or.inl ⟨h', h⟩)
    · rcases hB h' with ht | ht'
      · exact Or.inr (Or.inr ⟨ts1 ht, h, ht⟩)
      · exact absurd (to2 ht') (ho2 h)

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A₁ B A₂ : Finset V) (hAB : IsSeparation G A₁ B A₂)
    (TL XB TR : Finset V) (hpart : IsPartition3 B TL XB TR)
    (k k₁ k₂ : ℕ) (hbudget : k₁ + k₂ + XB.card ≤ k + 1)
    (L₁ X₁ R₁ L₂ X₂ R₂ : Finset V)
    (h₁ : IsLeftPushed G (A₁ ∪ (B \ XB)) TL TR k₁ L₁ X₁ R₁)
    (h₂ : IsRightPushed G (A₂ ∪ (B \ XB)) TL TR k₂ L₂ X₂ R₂) :
    IsTerminalSep G Finset.univ TL TR (k + 1) (L₁ ∪ TL ∪ L₂) (X₁ ∪ XB ∪ X₂) (R₁ ∪ TR ∪ R₂) := by
  obtain ⟨⟨hp1, hTL1, hTR1, hne1, hc1⟩, -⟩ := h₁
  obtain ⟨⟨hp2, hTL2, hTR2, hne2, hc2⟩, -⟩ := h₂
  have hA := p3_iff.mp hAB.1
  have hB := p3_iff.mp hpart
  have hP1 := p3_iff.mp hp1
  have hP2 := p3_iff.mp hp2
  have hmemW1 : ∀ v, v ∈ A₁ ∪ (B \ XB) ↔ v ∈ A₁ ∨ (v ∈ B ∧ v ∉ XB) := by
    intro v; simp only [Finset.mem_union, Finset.mem_sdiff]
  have hmemW2 : ∀ v, v ∈ A₂ ∪ (B \ XB) ↔ v ∈ A₂ ∨ (v ∈ B ∧ v ∉ XB) := by
    intro v; simp only [Finset.mem_union, Finset.mem_sdiff]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [p3_iff]
    intro v
    have e1 := hA v
    simp only [Finset.mem_univ, iff_true] at e1
    have := glue_part (v ∈ A₁) (v ∈ B) (v ∈ A₂) (v ∈ TL) (v ∈ XB) (v ∈ TR)
      (v ∈ L₁) (v ∈ X₁) (v ∈ R₁) (v ∈ L₂) (v ∈ X₂) (v ∈ R₂) e1 (hB v)
      (by rw [← hmemW1]; exact hP1 v) (by rw [← hmemW2]; exact hP2 v)
      (fun h => hTL1 h) (fun h => hTR1 h) (fun h => hTL2 h) (fun h => hTR2 h)
    simp only [Finset.mem_univ, iff_true, Finset.mem_union]
    exact this
  · intro v hv
    simp only [Finset.mem_union]
    exact Or.inl (Or.inr hv)
  · intro v hv
    simp only [Finset.mem_union]
    exact Or.inl (Or.inr hv)
  · -- no edges
    have cls : ∀ a, a ∈ L₁ ∪ TL ∪ L₂ →
        (a ∈ A₁ ∧ a ∈ L₁) ∨ (a ∈ A₂ ∧ a ∈ L₂) ∨ (a ∈ L₁ ∧ a ∈ L₂ ∧ a ∈ TL) := by
      intro a ha
      have e1 : (a ∈ L₁ ∨ a ∈ X₁ ∨ a ∈ R₁ ↔ a ∈ A₁ ∨ (a ∈ B ∧ a ∉ XB)) := by
        rw [← hmemW1]; exact (hP1 a).1
      have e2 : (a ∈ L₂ ∨ a ∈ X₂ ∨ a ∈ R₂ ↔ a ∈ A₂ ∨ (a ∈ B ∧ a ∉ XB)) := by
        rw [← hmemW2]; exact (hP2 a).1
      have hB' : a ∈ B ∧ a ∉ XB → a ∈ TL ∨ a ∈ TR := by
        intro ⟨h1, h2⟩
        rcases (hB a).1.mpr h1 with h | h | h
        · exact Or.inl h
        · exact absurd h h2
        · exact Or.inr h
      refine glue_cls (a ∈ A₁) (a ∈ A₂) (a ∈ B) (a ∈ XB) (a ∈ L₁) (a ∈ L₂) (a ∈ TL) (a ∈ TR)
        (a ∈ R₁) (a ∈ R₂) (fun h => hTL1 h) (fun h => hTL2 h) (fun h => hTR1 h)
        (fun h => hTR2 h) hB' ?_ ?_ ?_ ?_ (by simpa only [Finset.mem_union] using ha)
      · intro h; exact e1.mp (Or.inl h)
      · intro h; exact e2.mp (Or.inl h)
      · intro h h'; exact (hP1 a).2.2.1 ⟨h, h'⟩
      · intro h h'; exact (hP2 a).2.2.1 ⟨h, h'⟩
    have clsR : ∀ a, a ∈ R₁ ∪ TR ∪ R₂ →
        (a ∈ A₁ ∧ a ∈ R₁) ∨ (a ∈ A₂ ∧ a ∈ R₂) ∨ (a ∈ R₁ ∧ a ∈ R₂ ∧ a ∈ TR) := by
      intro a ha
      have e1 : (a ∈ L₁ ∨ a ∈ X₁ ∨ a ∈ R₁ ↔ a ∈ A₁ ∨ (a ∈ B ∧ a ∉ XB)) := by
        rw [← hmemW1]; exact (hP1 a).1
      have e2 : (a ∈ L₂ ∨ a ∈ X₂ ∨ a ∈ R₂ ↔ a ∈ A₂ ∨ (a ∈ B ∧ a ∉ XB)) := by
        rw [← hmemW2]; exact (hP2 a).1
      have hB' : a ∈ B ∧ a ∉ XB → a ∈ TR ∨ a ∈ TL := by
        intro ⟨h1, h2⟩
        rcases (hB a).1.mpr h1 with h | h | h
        · exact Or.inr h
        · exact absurd h h2
        · exact Or.inl h
      refine glue_cls (a ∈ A₁) (a ∈ A₂) (a ∈ B) (a ∈ XB) (a ∈ R₁) (a ∈ R₂) (a ∈ TR) (a ∈ TL)
        (a ∈ L₁) (a ∈ L₂) (fun h => hTR1 h) (fun h => hTR2 h) (fun h => hTL1 h)
        (fun h => hTL2 h) hB' ?_ ?_ ?_ ?_ (by simpa only [Finset.mem_union] using ha)
      · intro h; exact e1.mp (Or.inr (Or.inr h))
      · intro h; exact e2.mp (Or.inr (Or.inr h))
      · intro h h'; exact (hP1 a).2.2.1 ⟨h', h⟩
      · intro h h'; exact (hP2 a).2.2.1 ⟨h', h⟩
    intro a ha b hb
    rcases cls a ha with ⟨a1, a2⟩ | ⟨a1, a2⟩ | ⟨a1, a2, a3⟩ <;>
      rcases clsR b hb with ⟨b1, b2⟩ | ⟨b1, b2⟩ | ⟨b1, b2, b3⟩
    · exact hne1 a a2 b b2
    · exact hAB.2 a a1 b b1
    · exact hne1 a a2 b b1
    · intro hadj; exact hAB.2 b b1 a a1 hadj.symm
    · exact hne2 a a2 b b2
    · exact hne2 a a2 b b2
    · exact hne1 a a1 b b2
    · exact hne2 a a2 b b2
    · exact hne1 a a1 b b1
  · calc (X₁ ∪ XB ∪ X₂).card ≤ (X₁ ∪ XB).card + X₂.card := Finset.card_union_le _ _
      _ ≤ X₁.card + XB.card + X₂.card := by
          have := Finset.card_union_le X₁ XB
          omega
      _ ≤ k + 1 := by omega
