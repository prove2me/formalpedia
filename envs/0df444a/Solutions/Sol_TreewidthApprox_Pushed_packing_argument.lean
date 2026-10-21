-- Prove2me | solution 1 for TreewidthApprox.Pushed.packing_argument
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:29:29.286978+00:00
-- url     : https://prove2.me/submissions/d5f32e39-1360-4504-93f0-d819ce03beba

import Mathlib
import Definitions.Def_TreewidthApprox_Pushed_Setting

set_option autoImplicit false
open TreewidthApprox.Pushed

theorem greedy {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℕ) (m : ℕ)
    (hw : ∀ i ∈ s, 2 * w i ≤ m) :
    (∃ A ⊆ s, m ≤ 3 * ∑ i ∈ A, w i ∧ 3 * ∑ i ∈ A, w i ≤ 2 * m) ∨ 3 * ∑ i ∈ s, w i < m := by
  induction s using Finset.induction_on with
  | empty =>
    rcases Nat.eq_zero_or_pos m with h | h
    · left; exact ⟨∅, Finset.Subset.refl _, by simp [h], by simp⟩
    · right; simpa using h
  | insert i s hi ih =>
    have hw' : ∀ j ∈ s, 2 * w j ≤ m := fun j hj => hw j (Finset.mem_insert_of_mem hj)
    have hwi : 2 * w i ≤ m := hw i (Finset.mem_insert_self _ _)
    rcases ih hw' with ⟨A, hA, h1, h2⟩ | h
    · left
      exact ⟨A, hA.trans (Finset.subset_insert _ _), h1, h2⟩
    · rw [Finset.sum_insert hi]
      by_cases hmi : m ≤ 3 * w i
      · left
        refine ⟨{i}, by simp, by simpa using hmi, by simp; omega⟩
      · by_cases hs : 3 * (w i + ∑ j ∈ s, w j) < m
        · right; exact hs
        · left
          refine ⟨insert i s, Finset.Subset.refl _, ?_, ?_⟩
          · rw [Finset.sum_insert hi]; omega
          · rw [Finset.sum_insert hi]; omega

theorem split_blocks {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℕ) (m : ℕ)
    (hw : ∀ i ∈ s, 2 * w i ≤ m) (hSum : ∑ i ∈ s, w i ≤ m) :
    ∃ A ⊆ s, 3 * ∑ i ∈ A, w i ≤ 2 * m ∧ 3 * ∑ i ∈ s \ A, w i ≤ 2 * m := by
  rcases greedy s w m hw with ⟨A, hA, h1, h2⟩ | h
  · refine ⟨A, hA, h2, ?_⟩
    have := Finset.sum_sdiff hA (f := w)
    omega
  · refine ⟨s, Finset.Subset.refl _, by omega, by simp⟩

section
variable {V : Type} [Fintype V] [DecidableEq V]

theorem mem_avoidComp' (G : SimpleGraph V) (X : Finset V) (u v : V) :
    v ∈ avoidComp G X u ↔ AvoidReach G X u v := by
  unfold avoidComp
  simp

theorem avoid_start {G : SimpleGraph V} {X : Finset V} {u v : V} (h : AvoidReach G X u v) :
    u ∉ X := by
  obtain ⟨p, hp⟩ := h
  exact hp u p.start_mem_support

theorem avoid_end {G : SimpleGraph V} {X : Finset V} {u v : V} (h : AvoidReach G X u v) :
    v ∉ X := by
  obtain ⟨p, hp⟩ := h
  exact hp v p.end_mem_support

theorem avoid_refl {G : SimpleGraph V} {X : Finset V} {u : V} (hu : u ∉ X) :
    AvoidReach G X u u := ⟨SimpleGraph.Walk.nil, by simp [hu]⟩

theorem avoid_symm {G : SimpleGraph V} {X : Finset V} {u v : V} (h : AvoidReach G X u v) :
    AvoidReach G X v u := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa [SimpleGraph.Walk.support_reverse] using hp⟩

theorem avoid_trans {G : SimpleGraph V} {X : Finset V} {u v w : V} (h : AvoidReach G X u v)
    (h' : AvoidReach G X v w) : AvoidReach G X u w := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := h'
  refine ⟨p.append q, fun x hx => ?_⟩
  rw [SimpleGraph.Walk.support_append] at hx
  rcases List.mem_append.mp hx with h1 | h1
  · exact hp x h1
  · exact hq x (List.mem_of_mem_tail h1)

theorem avoid_edge {G : SimpleGraph V} {X : Finset V} {a b : V} (hab : G.Adj a b)
    (ha : a ∉ X) (hb : b ∉ X) : AvoidReach G X a b :=
  ⟨SimpleGraph.Walk.cons hab SimpleGraph.Walk.nil, by
    intro x hx
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ha
    · exact hb⟩

theorem comp_eq_of_mem (G : SimpleGraph V) (X : Finset V) {u₁ u₂ v : V}
    (h1 : v ∈ avoidComp G X u₁) (h2 : v ∈ avoidComp G X u₂) :
    avoidComp G X u₁ = avoidComp G X u₂ := by
  rw [mem_avoidComp'] at h1 h2
  have h12 : AvoidReach G X u₁ u₂ := avoid_trans h1 (avoid_symm h2)
  ext w
  rw [mem_avoidComp', mem_avoidComp']
  exact ⟨fun h => avoid_trans (avoid_symm h12) h, fun h => avoid_trans h12 h⟩

theorem solution (G : SimpleGraph V)
    (S X' : Finset V)
    (hX' : ∀ u : V, u ∉ X' → 2 * (avoidComp G X' u ∩ S).card ≤ S.card) :
    ∃ Lft Rgt : Finset V, Disjoint Lft Rgt ∧ Lft ∪ Rgt = Finset.univ \ X' ∧
      NoEdge G Lft Rgt ∧
      3 * (Lft ∩ S).card ≤ 2 * S.card ∧ 3 * (Rgt ∩ S).card ≤ 2 * S.card := by
  set 𝒞 : Finset (Finset V) := (Finset.univ.filter (fun u => u ∉ X')).image (avoidComp G X')
    with h𝒞
  have hmemC : ∀ C, C ∈ 𝒞 ↔ ∃ u, u ∉ X' ∧ avoidComp G X' u = C := by
    intro C; simp [h𝒞]
  have hCsub : ∀ C ∈ 𝒞, ∀ v ∈ C, v ∉ X' := by
    intro C hC v hv
    obtain ⟨u, hu, rfl⟩ := (hmemC C).mp hC
    exact avoid_end ((mem_avoidComp' G X' u v).mp hv)
  have hdisj : ∀ C₁ ∈ 𝒞, ∀ C₂ ∈ 𝒞, ∀ v, v ∈ C₁ → v ∈ C₂ → C₁ = C₂ := by
    intro C₁ h₁ C₂ h₂ v hv₁ hv₂
    obtain ⟨u₁, hu₁, rfl⟩ := (hmemC C₁).mp h₁
    obtain ⟨u₂, hu₂, rfl⟩ := (hmemC C₂).mp h₂
    exact comp_eq_of_mem G X' hv₁ hv₂
  have hpd : ∀ T : Finset (Finset V), T ⊆ 𝒞 →
      (T : Set (Finset V)).PairwiseDisjoint (fun C => C ∩ S) := by
    intro T hT C₁ h₁ C₂ h₂ hne
    show Disjoint (C₁ ∩ S) (C₂ ∩ S)
    refine Finset.disjoint_left.mpr fun v hv₁ hv₂ => hne ?_
    exact hdisj C₁ (hT h₁) C₂ (hT h₂) v (Finset.mem_inter.mp hv₁).1 (Finset.mem_inter.mp hv₂).1
  have hw : ∀ C ∈ 𝒞, 2 * (C ∩ S).card ≤ S.card := by
    intro C hC
    obtain ⟨u, hu, rfl⟩ := (hmemC C).mp hC
    exact hX' u hu
  have hsum : ∀ T : Finset (Finset V), T ⊆ 𝒞 →
      (T.biUnion (fun C => C ∩ S)).card = ∑ C ∈ T, (C ∩ S).card := fun T hT =>
    Finset.card_biUnion (hpd T hT)
  have hSum : ∑ C ∈ 𝒞, (C ∩ S).card ≤ S.card := by
    rw [← hsum 𝒞 (Finset.Subset.refl _)]
    exact Finset.card_le_card (Finset.biUnion_subset.mpr fun C _ => Finset.inter_subset_right)
  obtain ⟨A, hAs, hA1, hA2⟩ := split_blocks 𝒞 (fun C => (C ∩ S).card) S.card hw hSum
  have hRs : 𝒞 \ A ⊆ 𝒞 := Finset.sdiff_subset
  refine ⟨A.biUnion id, (𝒞 \ A).biUnion id, ?_, ?_, ?_, ?_, ?_⟩
  · refine Finset.disjoint_left.mpr fun v hv₁ hv₂ => ?_
    obtain ⟨C₁, hC₁, hv₁⟩ := Finset.mem_biUnion.mp hv₁
    obtain ⟨C₂, hC₂, hv₂⟩ := Finset.mem_biUnion.mp hv₂
    have := hdisj C₁ (hAs hC₁) C₂ (hRs hC₂) v hv₁ hv₂
    subst this
    exact (Finset.mem_sdiff.mp hC₂).2 hC₁
  · ext v
    simp only [Finset.mem_union, Finset.mem_biUnion, id, Finset.mem_sdiff, Finset.mem_univ,
      true_and]
    constructor
    · rintro (⟨C, hC, hv⟩ | ⟨C, hC, hv⟩)
      · exact hCsub C (hAs hC) v hv
      · exact hCsub C hC.1 v hv
    · intro hv
      have hC : avoidComp G X' v ∈ 𝒞 := (hmemC _).mpr ⟨v, hv, rfl⟩
      have hvC : v ∈ avoidComp G X' v := (mem_avoidComp' G X' v v).mpr (avoid_refl hv)
      by_cases hA : avoidComp G X' v ∈ A
      · exact Or.inl ⟨_, hA, hvC⟩
      · exact Or.inr ⟨_, ⟨hC, hA⟩, hvC⟩
  · intro a ha b hb hadj
    obtain ⟨C₁, hC₁, ha⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨C₂, hC₂, hb⟩ := Finset.mem_biUnion.mp hb
    simp only [id] at ha hb
    obtain ⟨u, hu, rfl⟩ := (hmemC C₁).mp (hAs hC₁)
    have hra : AvoidReach G X' u a := (mem_avoidComp' G X' u a).mp ha
    have hbX : b ∉ X' := hCsub C₂ (hRs hC₂) b hb
    have hrb : AvoidReach G X' u b :=
      avoid_trans hra (avoid_edge hadj (avoid_end hra) hbX)
    have hbC : b ∈ avoidComp G X' u := (mem_avoidComp' G X' u b).mpr hrb
    have := hdisj _ (hAs hC₁) C₂ (hRs hC₂) b hbC hb
    subst this
    exact (Finset.mem_sdiff.mp hC₂).2 hC₁
  · have e : (A.biUnion id) ∩ S = A.biUnion (fun C => C ∩ S) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_biUnion, id]
      constructor
      · rintro ⟨⟨C, hC, hv⟩, hS⟩
        exact ⟨C, hC, hv, hS⟩
      · rintro ⟨C, hC, hv, hS⟩
        exact ⟨⟨C, hC, hv⟩, hS⟩
    rw [e, hsum A hAs]
    exact hA1
  · have e : ((𝒞 \ A).biUnion id) ∩ S = (𝒞 \ A).biUnion (fun C => C ∩ S) := by
      ext v
      simp only [Finset.mem_inter, Finset.mem_biUnion, id]
      constructor
      · rintro ⟨⟨C, hC, hv⟩, hS⟩
        exact ⟨C, hC, hv, hS⟩
      · rintro ⟨C, hC, hv, hS⟩
        exact ⟨⟨C, hC, hv⟩, hS⟩
    rw [e, hsum (𝒞 \ A) hRs]
    exact hA2
end
