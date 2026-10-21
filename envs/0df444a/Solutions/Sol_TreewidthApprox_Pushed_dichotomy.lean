-- Prove2me | solution 1 for TreewidthApprox.Pushed.dichotomy
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:23:04.023545+00:00
-- url     : https://prove2.me/submissions/1463e9f0-3dd8-495a-81bd-5025abe3de5f

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


theorem card3 {V : Type} [DecidableEq V] {W P Q R : Finset V} (hp : IsPartition3 W P Q R)
    (S : Finset V) (hS : S ⊆ W) :
    S.card = (S ∩ P).card + (S ∩ Q).card + (S ∩ R).card := by
  have h := p3_iff.mp hp
  have e : S = (S ∩ P) ∪ (S ∩ Q) ∪ (S ∩ R) := by
    ext v
    have := h v
    have hv := @hS v
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · intro hv'
      have := this.1.mpr (hv hv')
      tauto
    · intro hh; tauto
  have d1 : Disjoint (S ∩ P) (S ∩ Q) := by
    refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
    have := h v
    simp only [Finset.mem_inter] at h1 h2
    tauto
  have d2 : Disjoint ((S ∩ P) ∪ (S ∩ Q)) (S ∩ R) := by
    refine Finset.disjoint_left.mpr fun v h1 h2 => ?_
    have := h v
    simp only [Finset.mem_union, Finset.mem_inter] at h1 h2
    tauto
  have h' := congrArg Finset.card e
  rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1] at h'
  exact h'

theorem four_ineq {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (A₁ B A₂ : Finset V) (hAB : IsSeparation G A₁ B A₂)
    (hA₁ : (A₁.card : ℝ) ≤ 3 / 4 * Fintype.card V) (hA₂ : (A₂.card : ℝ) ≤ 3 / 4 * Fintype.card V)
    (L X R : Finset V) (hLXR : IsSeparation G L X R) (hX : X.card ≤ k + 1)
    (hL : (L.card : ℝ) ≤ 2 / 3 * Fintype.card V) (hR : (R.card : ℝ) ≤ 2 / 3 * Fintype.card V) :
    ((L ∩ A₁).card : ℝ) + (L ∩ A₂).card + B.card ≥ 1 / 3 * Fintype.card V - (k + 1) ∧
      ((R ∩ A₁).card : ℝ) + (R ∩ A₂).card + B.card ≥ 1 / 3 * Fintype.card V - (k + 1) ∧
      ((L ∩ A₁).card : ℝ) + (R ∩ A₁).card + (k + 1) ≥ 1 / 4 * Fintype.card V - B.card ∧
      ((L ∩ A₂).card : ℝ) + (R ∩ A₂).card + (k + 1) ≥ 1 / 4 * Fintype.card V - B.card := by
  have hn1 : Fintype.card V = A₁.card + B.card + A₂.card := by
    have := card3 hAB.1 Finset.univ (Finset.Subset.refl _)
    simpa [Finset.card_univ] using this
  have hn2 : Fintype.card V = L.card + X.card + R.card := by
    have := card3 hLXR.1 Finset.univ (Finset.Subset.refl _)
    simpa [Finset.card_univ] using this
  have hLc := card3 hAB.1 L (Finset.subset_univ _)
  have hRc := card3 hAB.1 R (Finset.subset_univ _)
  have hA1c := card3 hLXR.1 A₁ (Finset.subset_univ _)
  have hA2c := card3 hLXR.1 A₂ (Finset.subset_univ _)
  rw [Finset.inter_comm A₁ L, Finset.inter_comm A₁ X, Finset.inter_comm A₁ R] at hA1c
  rw [Finset.inter_comm A₂ L, Finset.inter_comm A₂ X, Finset.inter_comm A₂ R] at hA2c
  have hLB : (L ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
  have hRB : (R ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
  have hX1 : (X ∩ A₁).card ≤ X.card := Finset.card_le_card Finset.inter_subset_left
  have hX2 : (X ∩ A₂).card ≤ X.card := Finset.card_le_card Finset.inter_subset_left
  have c1 : (L.card : ℝ) = (L ∩ A₁).card + (L ∩ B).card + (L ∩ A₂).card := by exact_mod_cast hLc
  have c2 : (R.card : ℝ) = (R ∩ A₁).card + (R ∩ B).card + (R ∩ A₂).card := by exact_mod_cast hRc
  have c3 : (A₁.card : ℝ) = (L ∩ A₁).card + (X ∩ A₁).card + (R ∩ A₁).card := by
    exact_mod_cast hA1c
  have c4 : (A₂.card : ℝ) = (L ∩ A₂).card + (X ∩ A₂).card + (R ∩ A₂).card := by
    exact_mod_cast hA2c
  have d1 : ((L ∩ B).card : ℝ) ≤ B.card := by exact_mod_cast hLB
  have d2 : ((R ∩ B).card : ℝ) ≤ B.card := by exact_mod_cast hRB
  have d3 : ((X ∩ A₁).card : ℝ) ≤ k + 1 := by exact_mod_cast hX1.trans hX
  have d4 : ((X ∩ A₂).card : ℝ) ≤ k + 1 := by exact_mod_cast hX2.trans hX
  have d5 : (X.card : ℝ) ≤ k + 1 := by exact_mod_cast hX
  have hn1' : (Fintype.card V : ℝ) = A₁.card + B.card + A₂.card := by exact_mod_cast hn1
  have hn2' : (Fintype.card V : ℝ) = L.card + X.card + R.card := by exact_mod_cast hn2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem solution {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (k : ℕ) (A₁ B A₂ : Finset V) (hAB : IsSeparation G A₁ B A₂)
    (hA₁ : (A₁.card : ℝ) ≤ 3 / 4 * Fintype.card V) (hA₂ : (A₂.card : ℝ) ≤ 3 / 4 * Fintype.card V)
    (L X R : Finset V) (hLXR : IsSeparation G L X R) (hX : X.card ≤ k + 1)
    (hL : (L.card : ℝ) ≤ 2 / 3 * Fintype.card V) (hR : (R.card : ℝ) ≤ 2 / 3 * Fintype.card V) :
    ((1 / 8 * (Fintype.card V : ℝ) - ((B.card : ℝ) + (k + 1)) / 2) ≤ (L ∩ A₁).card ∧
        (1 / 8 * (Fintype.card V : ℝ) - ((B.card : ℝ) + (k + 1)) / 2) ≤ (R ∩ A₂).card) ∨
      ((1 / 8 * (Fintype.card V : ℝ) - ((B.card : ℝ) + (k + 1)) / 2) ≤ (L ∩ A₂).card ∧
        (1 / 8 * (Fintype.card V : ℝ) - ((B.card : ℝ) + (k + 1)) / 2) ≤ (R ∩ A₁).card) := by
  obtain ⟨h1, h2, h3, h4⟩ := four_ineq G k A₁ B A₂ hAB hA₁ hA₂ L X R hLXR hX hL hR
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  by_contra hcon
  push_neg at hcon
  obtain ⟨c1, c2⟩ := hcon
  by_cases hl1 : (1 / 8 * (Fintype.card V : ℝ) - ((B.card : ℝ) + (k + 1)) / 2) ≤ (L ∩ A₁).card
  · have hr2 := c1 hl1
    by_cases hl2 : (1 / 8 * (Fintype.card V : ℝ) - ((B.card : ℝ) + (k + 1)) / 2) ≤ (L ∩ A₂).card
    · have := c2 hl2
      linarith
    · push_neg at hl2
      linarith
  · push_neg at hl1
    by_cases hl2 : (1 / 8 * (Fintype.card V : ℝ) - ((B.card : ℝ) + (k + 1)) / 2) ≤ (L ∩ A₂).card
    · have := c2 hl2
      linarith
    · push_neg at hl2
      linarith
