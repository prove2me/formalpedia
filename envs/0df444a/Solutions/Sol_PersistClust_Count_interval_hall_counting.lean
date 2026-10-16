-- Prove2me | solution 1 for PersistClust.Count.interval_hall_counting
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T22:12:00.604096+00:00
-- url     : https://prove2.me/submissions/bff872ed-ab8f-40b1-8114-9773a81d436d

import Mathlib

private theorem ih_interval_hall_aux {X Q α : Type} [LinearOrder α] (lo hi : X → α) (pos : Q → α) :
    ∀ (n : ℕ) (s : Finset X), s.card ≤ n → (∀ x ∈ s, lo x ≤ hi x) →
    (∀ A B : α, A ≤ B → {x ∈ (s : Set X) | A ≤ lo x ∧ hi x ≤ B}.encard ≤
        {q : Q | A ≤ pos q ∧ pos q ≤ B}.encard) →
    (s : Set X).encard ≤ (⋃ x ∈ (s : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x}).encard := by
  intro n
  induction n with
  | zero =>
    intro s hs _ _
    have h0 : s = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hs)
    subst h0; simp
  | succ n ih =>
    intro s hcard hlohi hwin
    rcases s.eq_empty_or_nonempty with h | hne
    · subst h; simp
    obtain ⟨x0, hx0, hA⟩ := s.exists_mem_eq_inf' hne lo
    obtain ⟨x1, hx1, hB⟩ := s.exists_mem_eq_sup' hne hi
    by_cases hcov : ∀ q : Q, s.inf' hne lo ≤ pos q → pos q ≤ s.sup' hne hi →
        q ∈ ⋃ x ∈ (s : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x}
    · have hAB : s.inf' hne lo ≤ s.sup' hne hi :=
        le_trans (Finset.inf'_le _ hx0) (le_trans (hlohi x0 hx0) (Finset.le_sup' _ hx0))
      have h1 : (s : Set X) ⊆
          {x ∈ (s : Set X) | s.inf' hne lo ≤ lo x ∧ hi x ≤ s.sup' hne hi} :=
        fun x hx => ⟨hx, Finset.inf'_le _ hx, Finset.le_sup' _ hx⟩
      calc (s : Set X).encard ≤ _ := Set.encard_le_encard h1
        _ ≤ _ := hwin _ _ hAB
        _ ≤ _ := Set.encard_le_encard (fun q hq => hcov q hq.1 hq.2)
    · push Not at hcov
      obtain ⟨q, hqA, hqB, hqN⟩ := hcov
      have hsep : ∀ x ∈ s, hi x < pos q ∨ pos q < lo x := by
        intro x hx
        by_contra hc
        push Not at hc
        exact hqN (Set.mem_biUnion (Finset.mem_coe.mpr hx) ⟨hc.2, hc.1⟩)
      have hx0L : hi x0 < pos q := by
        rcases hsep x0 hx0 with h | h
        · exact h
        · exact absurd (hA ▸ hqA) (not_le.mpr h)
      have hx1R : pos q < lo x1 := by
        rcases hsep x1 hx1 with h | h
        · exact absurd (hB ▸ hqB) (not_le.mpr h)
        · exact h
      set L := s.filter (fun x => hi x < pos q) with hLdef
      set R := s.filter (fun x => pos q < lo x) with hRdef
      have hLc : L.card ≤ n := by
        have : L.card < s.card := Finset.card_lt_card
          (Finset.filter_ssubset.mpr ⟨x1, hx1, fun h => absurd (lt_trans h (lt_of_lt_of_le hx1R
            (hlohi x1 hx1))) (lt_irrefl _)⟩)
        omega
      have hRc : R.card ≤ n := by
        have : R.card < s.card := Finset.card_lt_card
          (Finset.filter_ssubset.mpr ⟨x0, hx0, fun h => absurd (lt_trans h (lt_of_le_of_lt
            (hlohi x0 hx0) hx0L)) (lt_irrefl _)⟩)
        omega
      have hLs : L ⊆ s := Finset.filter_subset _ _
      have hRs : R ⊆ s := Finset.filter_subset _ _
      have hL := ih L hLc (fun x hx => hlohi x (hLs hx)) (fun A B hAB => by
        refine le_trans (Set.encard_le_encard ?_) (hwin A B hAB)
        intro x hx; exact ⟨Finset.mem_coe.mpr (hLs hx.1), hx.2⟩)
      have hR := ih R hRc (fun x hx => hlohi x (hRs hx)) (fun A B hAB => by
        refine le_trans (Set.encard_le_encard ?_) (hwin A B hAB)
        intro x hx; exact ⟨Finset.mem_coe.mpr (hRs hx.1), hx.2⟩)
      have hcovs : (s : Set X) ⊆ (L : Set X) ∪ (R : Set X) := by
        intro x hx
        rcases hsep x hx with h | h
        · exact Or.inl (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hx, h⟩))
        · exact Or.inr (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hx, h⟩))
      have hdisj : Disjoint (⋃ x ∈ (L : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x})
          (⋃ x ∈ (R : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x}) := by
        rw [Set.disjoint_left]
        intro r hr1 hr2
        obtain ⟨x, hx, hrx⟩ := Set.mem_iUnion₂.mp hr1
        obtain ⟨y, hy, hry⟩ := Set.mem_iUnion₂.mp hr2
        have h1 : hi x < pos q := (Finset.mem_filter.mp hx).2
        have h2 : pos q < lo y := (Finset.mem_filter.mp hy).2
        have h3 : pos r ≤ hi x := hrx.2
        have h4 : lo y ≤ pos r := hry.1
        exact absurd (lt_of_le_of_lt h4 (lt_of_le_of_lt h3 (lt_trans h1 h2))) (lt_irrefl _)
      have hsub : (⋃ x ∈ (L : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x}) ∪
          (⋃ x ∈ (R : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x}) ⊆
          ⋃ x ∈ (s : Set X), {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x} :=
        Set.union_subset (Set.biUnion_subset_biUnion_left (Finset.coe_subset.mpr hLs))
          (Set.biUnion_subset_biUnion_left (Finset.coe_subset.mpr hRs))
      calc (s : Set X).encard ≤ ((L : Set X) ∪ (R : Set X)).encard := Set.encard_le_encard hcovs
        _ ≤ (L : Set X).encard + (R : Set X).encard := Set.encard_union_le _ _
        _ ≤ _ := add_le_add hL hR
        _ = _ := (Set.encard_union_eq hdisj).symm
        _ ≤ _ := Set.encard_le_encard hsub

theorem solution {X Q : Type} (lo hi : X → ℝ) (pos : Q → ℝ)
    (s : Set X) (hs : s.Finite) (hlohi : ∀ x ∈ s, lo x ≤ hi x)
    (hwin : ∀ A B : ℝ, A ≤ B →
      {x ∈ s | A ≤ lo x ∧ hi x ≤ B}.encard ≤ {q : Q | A ≤ pos q ∧ pos q ≤ B}.encard) :
    s.encard ≤ (⋃ x ∈ s, {q : Q | lo x ≤ pos q ∧ pos q ≤ hi x}).encard := by
  obtain ⟨t, rfl⟩ := hs.exists_finset_coe
  exact ih_interval_hall_aux lo hi pos t.card t le_rfl hlohi hwin

