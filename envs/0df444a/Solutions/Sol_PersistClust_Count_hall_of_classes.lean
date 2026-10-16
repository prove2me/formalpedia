-- Prove2me | solution 1 for PersistClust.Count.hall_of_classes
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T20:53:20.138803+00:00
-- url     : https://prove2.me/submissions/7a3debaf-49fa-4b9d-80d9-73491b62422d

import Mathlib

/-- splitting a set by a predicate: encard is additive -/
private theorem hoc_encard_split_pred {S : Type} (s : Set S) (p : S -> Prop) :
    s.encard = {a ∈ s | p a}.encard + {a ∈ s | ¬ p a}.encard := by
  rw [← Set.encard_union_eq]
  · congr 1
    ext a
    by_cases h : p a <;> simp [h]
  · rw [Set.disjoint_left]
    intro a h1 h2
    exact h2.2 h1.2

/-- fiber unions of two sets with distinct classes are disjoint -/
private theorem hoc_fiber_union_disjoint {S T K : Type} (κ : S → K) (G : S → Set T)
    (hdisj : ∀ a a' : S, κ a ≠ κ a' → G a ∩ G a' = ∅) (s₁ s₂ : Set S)
    (h : ∀ a ∈ s₁, ∀ a' ∈ s₂, κ a ≠ κ a') :
    Disjoint (⋃ x ∈ s₁, G x) (⋃ x ∈ s₂, G x) := by
  rw [Set.disjoint_left]
  intro t h1 h2
  simp only [Set.mem_iUnion] at h1 h2
  obtain ⟨a, ha, hta⟩ := h1
  obtain ⟨a', ha', hta'⟩ := h2
  have := hdisj a a' (h a ha a' ha')
  have hmem : t ∈ G a ∩ G a' := ⟨hta, hta'⟩
  rw [this] at hmem
  exact hmem

/-- union of fibers over a predicate split -/
private theorem hoc_fiber_union_split {S T : Type} (G : S → Set T) (s : Set S) (p : S -> Prop) :
    (⋃ x ∈ s, G x) = (⋃ x ∈ {a ∈ s | p a}, G x) ∪ (⋃ x ∈ {a ∈ s | ¬ p a}, G x) := by
  rw [← Set.biUnion_union]
  congr 1
  ext a
  by_cases h : p a <;> simp [h]

/-- core induction over a finset of classes covering the image -/
private theorem hoc_hall_of_classes_aux {S T K : Type} (κ : S → K) (G : S → Set T)
    (hdisj : ∀ a a' : S, κ a ≠ κ a' → G a ∩ G a' = ∅)
    (hclass : ∀ s : Set S, s.Finite → (∀ a ∈ s, ∀ a' ∈ s, κ a = κ a') →
      s.encard ≤ (⋃ x ∈ s, G x).encard) (F : Finset K) :
    ∀ s : Set S, s.Finite → κ '' s ⊆ ↑F → s.encard ≤ (⋃ x ∈ s, G x).encard := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    intro s _ hsub
    have : s = ∅ := by
      rw [← Set.image_eq_empty (f := κ)]
      simpa using hsub
    subst this
    simp
  | insert k F _ ih =>
    intro s hs hsub
    rw [hoc_encard_split_pred s (fun a => κ a = k), hoc_fiber_union_split G s (fun a => κ a = k),
      Set.encard_union_eq (hoc_fiber_union_disjoint κ G hdisj _ _ ?_)]
    · apply add_le_add
      · apply hclass _ (hs.subset (fun a h => h.1))
        intro a ha a' ha'
        rw [ha.2, ha'.2]
      · apply ih _ (hs.subset (fun a h => h.1))
        rintro _ ⟨a, ha, rfl⟩
        have := hsub ⟨a, ha.1, rfl⟩
        simp only [Finset.coe_insert, Set.mem_insert_iff] at this
        exact this.resolve_left ha.2
    · intro a ha a' ha'
      rw [ha.2]
      exact fun h => ha'.2 h.symm

theorem solution {S T K : Type} (κ : S → K) (G : S → Set T)
    (hdisj : ∀ a a' : S, κ a ≠ κ a' → G a ∩ G a' = ∅)
    (hclass : ∀ s : Set S, s.Finite → (∀ a ∈ s, ∀ a' ∈ s, κ a = κ a') →
      s.encard ≤ (⋃ x ∈ s, G x).encard) :
    ∀ s : Set S, s.Finite → s.encard ≤ (⋃ x ∈ s, G x).encard := by
  intro s hs
  exact hoc_hall_of_classes_aux κ G hdisj hclass (hs.image κ).toFinset s hs (by simp)

