-- Prove2me | solution 1 for PersistClust.Count.telescope_finite
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-15T18:38:21.260834+00:00
-- url     : https://prove2.me/submissions/d8c5cc6c-c03d-483d-8459-b28419974d57

import Mathlib

/-- For a finite set of reals and a point z, some positive eta is below every
nonzero distance from z to the set. -/
private lemma tel_exists_gap (S : Finset ℝ) (z : ℝ) :
    ∃ η > 0, ∀ y ∈ S, y ≠ z → η < |y - z| := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S ha ih =>
    obtain ⟨η, hη, hS⟩ := ih
    by_cases haz : a = z
    · refine ⟨η, hη, ?_⟩
      intro y hy hyz
      rcases Finset.mem_insert.mp hy with h | h
      · exact absurd (h.trans haz) hyz
      · exact hS y h hyz
    · have hpos : 0 < |a - z| := abs_pos.mpr (sub_ne_zero.mpr haz)
      refine ⟨min η (|a - z| / 2), lt_min hη (by linarith), ?_⟩
      intro y hy hyz
      have h1 : min η (|a - z| / 2) ≤ η := min_le_left _ _
      have h2 : min η (|a - z| / 2) ≤ |a - z| / 2 := min_le_right _ _
      rcases Finset.mem_insert.mp hy with h | h
      · subst h; linarith
      · have := hS y h hyz; linarith

private lemma tel_aux (h : ℝ → ℕ) (m : ℝ → ℕ) (Z : Finset ℝ)
    (hconst : ∀ s t : ℝ, s ≤ t → (∀ z ∈ Z, z < s ∨ t < z) → h s = h t)
    (hjump : ∀ z ∈ Z, ∃ η₀ > 0, ∀ η, 0 < η → η < η₀ → h (z + η) = h (z - η) + m z)
    (D₁ : ℝ) (hD₁ : D₁ ∉ Z) :
    ∀ n : ℕ, ∀ D₂ : ℝ, (Z.filter (fun z => D₁ < z ∧ z < D₂)).card = n → D₁ ≤ D₂ →
      D₂ ∉ Z → h D₂ = h D₁ + ∑ z ∈ Z.filter (fun z => D₁ < z ∧ z < D₂), m z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro D₂ hcard hD hD₂
  rcases (Z.filter (fun z => D₁ < z ∧ z < D₂)).eq_empty_or_nonempty with hWe | hWne
  · rw [hWe, Finset.sum_empty, add_zero]
    symm
    apply hconst D₁ D₂ hD
    intro z hz
    have hz1 : z ≠ D₁ := fun e => hD₁ (by rw [← e]; exact hz)
    have hz2 : z ≠ D₂ := fun e => hD₂ (by rw [← e]; exact hz)
    have hnot : ¬ (D₁ < z ∧ z < D₂) := by
      intro hh
      have hmem : z ∈ Z.filter (fun z => D₁ < z ∧ z < D₂) := Finset.mem_filter.mpr ⟨hz, hh⟩
      rw [hWe] at hmem; simp at hmem
    rcases lt_or_ge z D₁ with h1 | h1
    · exact Or.inl h1
    · right
      have h1' : D₁ < z := lt_of_le_of_ne h1 (Ne.symm hz1)
      rcases lt_or_ge z D₂ with h2 | h2
      · exact absurd ⟨h1', h2⟩ hnot
      · exact lt_of_le_of_ne h2 (Ne.symm hz2)
  · obtain ⟨zs, hzsW, hle⟩ : ∃ zs ∈ Z.filter (fun z => D₁ < z ∧ z < D₂),
        ∀ y ∈ Z.filter (fun z => D₁ < z ∧ z < D₂), y ≤ zs :=
      ⟨_, Finset.max'_mem _ hWne, fun y hy => Finset.le_max' _ y hy⟩
    have hzsZ : zs ∈ Z := (Finset.mem_filter.mp hzsW).1
    have hzs1 : D₁ < zs := (Finset.mem_filter.mp hzsW).2.1
    have hzs2 : zs < D₂ := (Finset.mem_filter.mp hzsW).2.2
    obtain ⟨η₀, hη₀, hj⟩ := hjump zs hzsZ
    obtain ⟨η₁, hη₁, hgap⟩ := tel_exists_gap (insert D₁ (insert D₂ Z)) zs
    obtain ⟨η, hηa, hηb, hηpos⟩ : ∃ η, η ≤ η₀ / 2 ∧ η ≤ η₁ ∧ 0 < η :=
      ⟨min (η₀ / 2) η₁, min_le_left _ _, min_le_right _ _, lt_min (by linarith) hη₁⟩
    have hη_lt : η < η₀ := by linarith
    have gD₁ : η₁ < zs - D₁ := by
      have hg := hgap D₁ (by simp) (ne_of_lt hzs1)
      rwa [abs_sub_comm, abs_of_pos (by linarith)] at hg
    have gD₂ : η₁ < D₂ - zs := by
      have hg := hgap D₂ (by simp) (ne_of_gt hzs2)
      rwa [abs_of_pos (by linarith)] at hg
    have hA : h (zs + η) = h D₂ := by
      apply hconst (zs + η) D₂ (by linarith)
      intro z hz
      rcases le_or_gt z zs with h1 | h1
      · left; linarith
      · right
        rcases lt_or_ge z D₂ with h2 | h2
        · exfalso
          have hzW : z ∈ Z.filter (fun z => D₁ < z ∧ z < D₂) :=
            Finset.mem_filter.mpr ⟨hz, by linarith, h2⟩
          have := hle z hzW; linarith
        · exact lt_of_le_of_ne h2 (fun e => hD₂ (by rw [e]; exact hz))
    have hB : h (zs + η) = h (zs - η) + m zs := hj η hηpos hη_lt
    have hD₂'Z : zs - η ∉ Z := by
      intro hmem
      have hg := hgap (zs - η) (by simp [hmem]) (ne_of_lt (by linarith))
      rw [show zs - η - zs = -η by ring, abs_neg, abs_of_pos hηpos] at hg
      linarith
    have hfilt : Z.filter (fun z => D₁ < z ∧ z < zs - η) =
        (Z.filter (fun z => D₁ < z ∧ z < D₂)).erase zs := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hz, h1, h2⟩
        exact ⟨ne_of_lt (by linarith), hz, h1, by linarith⟩
      · rintro ⟨hne, hz, h1, h2⟩
        refine ⟨hz, h1, ?_⟩
        have hzle : z ≤ zs := hle z (Finset.mem_filter.mpr ⟨hz, h1, h2⟩)
        have hlt : z < zs := lt_of_le_of_ne hzle hne
        have hg := hgap z (by simp [hz]) hne
        rw [abs_of_neg (by linarith)] at hg
        linarith
    have hcard' : ((Z.filter (fun z => D₁ < z ∧ z < D₂)).erase zs).card < n := by
      rw [Finset.card_erase_of_mem hzsW, ← hcard]
      exact Nat.sub_lt (Finset.card_pos.mpr hWne) one_pos
    have hC := ih _ hcard' (zs - η) (by rw [hfilt]) (by linarith) hD₂'Z
    rw [hfilt] at hC
    rw [← hA, hB, hC, add_assoc, Finset.sum_erase_add _ _ hzsW]

theorem solution (h : ℝ → ℕ) (m : ℝ → ℕ) (Z : Finset ℝ)
    (hconst : ∀ s t : ℝ, s ≤ t → (∀ z ∈ Z, z < s ∨ t < z) → h s = h t)
    (hjump : ∀ z ∈ Z, ∃ η₀ > 0, ∀ η, 0 < η → η < η₀ → h (z + η) = h (z - η) + m z)
    {D₁ D₂ : ℝ} (hD : D₁ ≤ D₂) (hD₁ : D₁ ∉ Z) (hD₂ : D₂ ∉ Z) :
    h D₂ = h D₁ + ∑ z ∈ Z.filter (fun z => D₁ < z ∧ z < D₂), m z :=
  tel_aux h m Z hconst hjump D₁ hD₁ _ D₂ rfl hD hD₂

