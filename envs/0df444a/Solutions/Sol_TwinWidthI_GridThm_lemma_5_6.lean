-- Prove2me | solution 1 for TwinWidthI.GridThm.lemma_5_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:31:26.991016+00:00
-- url     : https://prove2.me/submissions/f9b2b327-75eb-45a5-b053-f2b4f5875405

import Mathlib
import Definitions.Def_TwinWidthI_GridThm_Setting

set_option autoImplicit false

namespace TwinWidthI.GridThm

theorem qqb_vh {A : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) A)
    (R : Finset (Fin n)) (C : Finset (Fin m)) (h : ¬ IsMixed M R C) :
    IsVertical M R C ∨ IsHorizontal M R C := by
  unfold IsMixed at h
  by_contra hc
  exact h ⟨fun h1 => hc (Or.inl h1), fun h2 => hc (Or.inr h2)⟩

theorem qqb_zone_union {A : Type*} {n m : ℕ} (M : Matrix (Fin n) (Fin m) A)
    (X X' : Finset (Fin n)) (C : Finset (Fin m)) (a b : Fin n) (ha : a ∈ X) (hb : b ∈ X')
    (h1 : ¬ IsMixed M X C) (h2 : ¬ IsMixed M X' C) (h3 : ¬ IsMixed M {a, b} C) :
    ¬ IsMixed M (X ∪ X') C := by
  have k1 := qqb_vh M X C h1
  have k2 := qqb_vh M X' C h2
  have k3 := qqb_vh M {a, b} C h3
  have hUV : (IsVertical M X C ∧ IsVertical M X' C ∧ IsVertical M {a, b} C) ∨ IsHorizontal M (X ∪ X') C := by
    unfold IsVertical IsHorizontal at *
    rcases k1 with vX | hX <;> rcases k2 with vX' | hX' <;> rcases k3 with vc | hc
    · exact Or.inl ⟨vX, vX', vc⟩
    all_goals right
    all_goals intro i hi j hj j' hj'
    all_goals rcases Finset.mem_union.1 hi with h | h
    · -- V V H, i in X
      rw [vX i h a ha j hj, vX i h a ha j' hj']
      exact hc a (by simp) j hj j' hj'
    · rw [vX' i h b hb j hj, vX' i h b hb j' hj']
      exact hc b (by simp) j hj j' hj'
    · -- V H V
      rw [vX i h a ha j hj, vX i h a ha j' hj']
      rw [vc a (by simp) b (by simp) j hj, vc a (by simp) b (by simp) j' hj']
      exact hX' b hb j hj j' hj'
    · exact hX' i h j hj j'  hj'
    · -- V H H
      rw [vX i h a ha j hj, vX i h a ha j' hj']
      exact hc a (by simp) j hj j' hj'
    · exact hX' i h j hj j' hj'
    · -- H V V
      exact hX i h j hj j' hj'
    · rw [vX' i h b hb j hj, vX' i h b hb j' hj']
      rw [← vc a (by simp) b (by simp) j hj, ← vc a (by simp) b (by simp) j' hj']
      exact hX a ha j hj j' hj'
    · -- H V H
      exact hX i h j hj j' hj'
    · rw [vX' i h b hb j hj, vX' i h b hb j' hj']
      exact hc b (by simp) j hj j' hj'
    · -- H H V
      exact hX i h j hj j' hj'
    · exact hX' i h j hj j' hj'
    · exact hX i h j hj j' hj'
    · exact hX' i h j hj j' hj'
  rintro ⟨hnv, hnh⟩
  rcases hUV with ⟨vX, vX', vc⟩ | hh
  · apply hnv
    intro i hi i' hi' j hj
    have e : ∀ i ∈ X ∪ X', M i j = M a j := by
      intro i hi
      rcases Finset.mem_union.1 hi with h | h
      · exact vX i h a ha j hj
      · rw [vX' i h b hb j hj, ← vc a (by simp) b (by simp) j hj]
    rw [e i hi, e i' hi']
  · exact hnh hh

end TwinWidthI.GridThm

open TwinWidthI.GridThm Classical in
theorem solution {A : Type*} [Fintype A] {n m : ℕ} (M : Matrix (Fin n) (Fin m) A)
    (R R' : Finpartition (Finset.univ : Finset (Fin n))) (hR : IsDivision R)
    (C : Finset (Fin m)) (hC : IsIntervalSet C)
    (X X' : Finset (Fin n)) (hX : X ∈ R.parts) (hX' : X' ∈ R.parts)
    (hcons : ∃ a ∈ X, ∃ b ∈ X', (∀ x ∈ X, x ≤ a) ∧ (∀ y ∈ X', b ≤ y) ∧ (a : ℕ) + 1 = b)
    (hR' : R'.parts = insert (X ∪ X') ((R.parts.erase X).erase X')) :
    mixedValueRow M R' C ≤ mixedValueRow M R C := by
  obtain ⟨a, haX, b, hbX', hamax, hbmin, hab⟩ := hcons
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (R.parts.erase X).erase X' := ⟨_, rfl⟩
  rw [← hQ] at hR'
  have hQmem : ∀ Y, Y ∈ Q ↔ Y ≠ X' ∧ Y ≠ X ∧ Y ∈ R.parts := by
    intro Y; rw [hQ]; simp [Finset.mem_erase]
  have hne : X ≠ X' := by
    intro h; subst h
    have := hamax b hbX'
    rw [Fin.le_def] at this; omega
  have hXQ : X ∉ insert X' Q := by
    intro h
    rcases Finset.mem_insert.1 h with h | h
    · exact hne h
    · exact ((hQmem X).1 h).2.1 rfl
  have hX'Q : X' ∉ Q := fun h => ((hQmem X').1 h).1 rfl
  have hUQ : X ∪ X' ∉ Q := by
    intro h
    rw [hQmem] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hd := R.disjoint h3 hX h2
    exact Finset.disjoint_left.1 hd (Finset.mem_union_left _ haX) haX
  have hPeq : R.parts = insert X (insert X' Q) := by
    have h1 : insert X' Q = R.parts.erase X := by
      rw [hQ]; exact Finset.insert_erase (Finset.mem_erase.2 ⟨hne.symm, hX'⟩)
    rw [h1, Finset.insert_erase hX]
  have sumP : ∀ h : Finset (Fin n) → ℕ,
      ∑ Y ∈ R.parts, h Y = h X + h X' + ∑ Y ∈ Q, h Y := by
    intro h
    conv_lhs => rw [hPeq]
    rw [Finset.sum_insert hXQ, Finset.sum_insert hX'Q]; ring
  have sumP' : ∀ h : Finset (Fin n) → ℕ,
      ∑ Y ∈ insert (X ∪ X') Q, h Y = h (X ∪ X') + ∑ Y ∈ Q, h Y := by
    intro h
    rw [Finset.sum_insert hUQ]
  unfold mixedValueRow
  rw [hR']
  simp only [Finset.card_filter]
  rw [sumP, sumP', sumP', sumP]
  have hXP : X ∈ R.parts := hX
  have hQsub : ∀ Y ∈ Q, Y ∈ R.parts := fun Y hY => ((hQmem Y).1 hY).2.2
  have hba : (a : ℕ) < b := by omega
  -- cuts of parts of Q
  have hQcut : ∑ Y ∈ Q, (if ∃ Y' ∈ insert (X ∪ X') Q, IsMixedCutRow M Y Y' C then 1 else 0) ≤
      ∑ Y ∈ Q, (if ∃ Y' ∈ R.parts, IsMixedCutRow M Y Y' C then 1 else 0) := by
    apply Finset.sum_le_sum
    intro Y hY
    have himp : (∃ Y' ∈ insert (X ∪ X') Q, IsMixedCutRow M Y Y' C) →
        (∃ Y' ∈ R.parts, IsMixedCutRow M Y Y' C) := by
      rintro ⟨Y', hY', a', ha', b', hb', h1, h2, h3, h4⟩
      rcases Finset.mem_insert.1 hY' with h | h
      · subst h
        rcases Finset.mem_union.1 hb' with hb'X | hb'X'
        · refine ⟨X, hX, a', ha', b', hb'X, h1, ?_, h3, h4⟩
          intro y hy; exact h2 y (Finset.mem_union_left _ hy)
        · refine ⟨X', hX', a', ha', b', hb'X', h1, ?_, h3, h4⟩
          intro y hy; exact h2 y (Finset.mem_union_right _ hy)
      · exact ⟨Y', hQsub Y' h, a', ha', b', hb', h1, h2, h3, h4⟩
    split_ifs with h1 h2 <;> first | exact le_refl _ | omega | exact absurd (himp h1) h2
  have hU : (if ∃ Y' ∈ insert (X ∪ X') Q, IsMixedCutRow M (X ∪ X') Y' C then 1 else 0) ≤
      (if ∃ Y' ∈ R.parts, IsMixedCutRow M X' Y' C then 1 else 0) := by
    have himp : (∃ Y' ∈ insert (X ∪ X') Q, IsMixedCutRow M (X ∪ X') Y' C) →
        (∃ Y' ∈ R.parts, IsMixedCutRow M X' Y' C) := by
      rintro ⟨Y', hY', a', ha', b', hb', h1, h2, h3, h4⟩
      rcases Finset.mem_insert.1 hY' with h | h
      · subst h
        have := h1 b' hb'
        rw [Fin.le_def] at this; omega
      · have ha'X' : a' ∈ X' := by
          rcases Finset.mem_union.1 ha' with h5 | h5
          · exfalso
            have e1 := h1 b (Finset.mem_union_right _ hbX')
            have e2 := hamax a' h5
            rw [Fin.le_def] at e1 e2; omega
          · exact h5
        exact ⟨Y', hQsub Y' h, a', ha'X', b', hb', fun x hx => h1 x (Finset.mem_union_right _ hx),
          h2, h3, h4⟩
    split_ifs with h1 h2 <;> first | exact le_refl _ | omega | exact absurd (himp h1) h2
  have hmix : (if IsMixed M (X ∪ X') C then 1 else 0) ≤ (if IsMixed M X C then 1 else 0) +
      (if IsMixed M X' C then 1 else 0) +
      (if ∃ Y' ∈ R.parts, IsMixedCutRow M X Y' C then 1 else 0) := by
    by_cases h1 : IsMixed M X C
    · simp [h1]; split_ifs <;> omega
    by_cases h2 : IsMixed M X' C
    · simp [h2]; split_ifs <;> omega
    by_cases h3 : ∃ Y' ∈ R.parts, IsMixedCutRow M X Y' C
    · simp [h3]; split_ifs <;> omega
    have h3' : ¬ IsMixed M {a, b} C := by
      intro hm
      exact h3 ⟨X', hX', a, haX, b, hbX', hamax, hbmin, hab, hm⟩
    have := qqb_zone_union M X X' C a b haX hbX' h1 h2 h3'
    simp [h1, h2, h3, this]
  omega

