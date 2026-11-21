-- Prove2me | solution 1 for ProConChoice.Rational.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-20T12:53:43.842111+00:00
-- url     : https://prove2.me/submissions/eb9e0173-21b6-4fdc-8f14-b550c46f25bb

import Mathlib

/-!
# Lemma 5 (Heller–Tompkins)

A real matrix all of whose entries are `0`, `1` or `-1`, with at most two nonzero entries per
column, whose rows are split into two parts `R` and its complement according to the sign rule,
is totally unimodular.

The proof is by strong induction on the size of a square submatrix, using the Laplace expansion
along a column: if a column is zero the determinant vanishes; if it has a single nonzero entry the
determinant reduces to a smaller minor; if every column has exactly two nonzero entries the rows
are linearly dependent.
-/

set_option maxHeartbeats 1000000

private lemma sign_mem_of_tri (x : ℝ) (h : x = 0 ∨ x = 1 ∨ x = -1) :
    x ∈ Set.range SignType.cast := by
  rcases h with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp⟩

private lemma sign_mul_mem {a b : ℝ}
    (ha : a ∈ Set.range SignType.cast) (hb : b ∈ Set.range SignType.cast) :
    a * b ∈ Set.range SignType.cast := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  exact ⟨s * t, by simp⟩

private lemma neg_one_pow_mem (k : ℕ) : (-1 : ℝ) ^ k ∈ Set.range SignType.cast := by
  rcases neg_one_pow_eq_or ℝ k with h | h
  · rw [h]; exact ⟨1, by simp⟩
  · rw [h]; exact ⟨-1, by simp⟩

private lemma tu_aux : ∀ (k : ℕ) (B : Matrix (Fin k) (Fin k) ℝ) (R : Set (Fin k)),
    (∀ i j, B i j = 0 ∨ B i j = 1 ∨ B i j = -1) →
    (∀ j, (Finset.univ.filter (fun i => B i j ≠ 0)).card ≤ 2) →
    (∀ j i i', i ≠ i' → 0 < B i j * B i' j → (i ∈ R ↔ i' ∉ R)) →
    (∀ j i i', i ≠ i' → B i j * B i' j < 0 → (i ∈ R ↔ i' ∈ R)) →
    B.det ∈ Set.range SignType.cast := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro B R h1B h2B h3B h4B
    classical
    rcases k with _ | n
    · exact ⟨1, by simp⟩
    let F : Fin (n + 1) → Finset (Fin (n + 1)) :=
      fun j => Finset.univ.filter (fun i => B i j ≠ 0)
    by_cases h2all : ∀ j, (F j).card = 2
    · -- every column has exactly two nonzero entries: the rows are linearly dependent
      have hcol : ∀ j : Fin (n + 1),
          ∑ i, (if i ∈ R then (-1 : ℝ) else 1) * B i j = 0 := by
        intro j
        obtain ⟨i₁, i₂, hne, hF⟩ := Finset.card_eq_two.mp (h2all j)
        have hi1 : B i₁ j ≠ 0 := by
          have : i₁ ∈ F j := by simp [hF]
          simpa [F] using this
        have hi2 : B i₂ j ≠ 0 := by
          have : i₂ ∈ F j := by simp [hF]
          simpa [F] using this
        have hB1 : B i₁ j = 1 ∨ B i₁ j = -1 := by
          rcases h1B i₁ j with h | h | h
          · exact absurd h hi1
          · exact Or.inl h
          · exact Or.inr h
        have hB2 : B i₂ j = 1 ∨ B i₂ j = -1 := by
          rcases h1B i₂ j with h | h | h
          · exact absurd h hi2
          · exact Or.inl h
          · exact Or.inr h
        have hεopp : (i₁ ∈ R ↔ i₂ ∉ R) →
            (if i₁ ∈ R then (-1 : ℝ) else 1) = -(if i₂ ∈ R then (-1 : ℝ) else 1) := by
          intro hR
          by_cases hm : i₁ ∈ R
          · have hm2 : i₂ ∉ R := hR.mp hm
            rw [if_pos hm, if_neg hm2]
          · have hm2 : i₂ ∈ R := by
              by_contra h2c
              exact hm (hR.mpr h2c)
            rw [if_neg hm, if_pos hm2]; norm_num
        have hεsame : (i₁ ∈ R ↔ i₂ ∈ R) →
            (if i₁ ∈ R then (-1 : ℝ) else 1) = (if i₂ ∈ R then (-1 : ℝ) else 1) := by
          intro hR
          by_cases hm : i₁ ∈ R
          · rw [if_pos hm, if_pos (hR.mp hm)]
          · rw [if_neg hm, if_neg (fun h => hm (hR.mpr h))]
        have hstep : ∑ i, (if i ∈ R then (-1 : ℝ) else 1) * B i j
            = ∑ i ∈ F j, (if i ∈ R then (-1 : ℝ) else 1) * B i j := by
          refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro x _ hx
          have h0 : B x j = 0 := by simpa [F] using hx
          simp [h0]
        rw [hstep, hF, Finset.sum_pair hne]
        rcases hB1 with h1' | h1' <;> rcases hB2 with h2' | h2'
        · have hR := h3B j i₁ i₂ hne (by rw [h1', h2']; norm_num)
          rw [h1', h2', hεopp hR]
          ring
        · have hR := h4B j i₁ i₂ hne (by rw [h1', h2']; norm_num)
          rw [h1', h2', hεsame hR]
          ring
        · have hR := h4B j i₁ i₂ hne (by rw [h1', h2']; norm_num)
          rw [h1', h2', hεsame hR]
          ring
        · have hR := h3B j i₁ i₂ hne (by rw [h1', h2']; norm_num)
          rw [h1', h2', hεopp hR]
          ring
      have hsum0 : ∑ i : Fin (n + 1), (if i ∈ R then (-1 : ℝ) else 1) • B i = 0 := by
        ext j
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        exact hcol j
      have hnz : ∃ i : Fin (n + 1), (if i ∈ R then (-1 : ℝ) else 1) ≠ 0 := by
        refine ⟨⟨0, Nat.succ_pos n⟩, ?_⟩
        split_ifs <;> norm_num
      have hni : ¬ LinearIndependent ℝ (fun i : Fin (n + 1) => B i) := by
        rw [Fintype.not_linearIndependent_iff]
        exact ⟨fun i => if i ∈ R then (-1 : ℝ) else 1, hsum0, hnz⟩
      rw [Matrix.det_eq_zero_of_not_linearIndependent_rows hni]
      exact ⟨0, by simp⟩
    · push_neg at h2all
      obtain ⟨j, hj⟩ := h2all
      have hle : (F j).card ≤ 2 := h2B j
      have hc : (F j).card = 0 ∨ (F j).card = 1 := by omega
      rcases hc with hc | hc
      · -- a zero column
        have hF0 : F j = ∅ := Finset.card_eq_zero.mp hc
        have hcol : ∀ i, B i j = 0 := by
          intro i
          have : i ∉ F j := by simp [hF0]
          simpa [F] using this
        rw [Matrix.det_eq_zero_of_column_eq_zero j hcol]
        exact ⟨0, by simp⟩
      · -- exactly one nonzero entry in column `j`
        obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hc
        have hzero : ∀ i, i ≠ i₀ → B i j = 0 := by
          intro i hi
          have hmem : i ∉ F j := by simp [hi₀, hi]
          simpa [F] using hmem
        rw [Matrix.det_succ_column B j]
        rw [Fintype.sum_eq_single i₀ (fun i hi => by simp [hzero i hi])]
        let C : Matrix (Fin n) (Fin n) ℝ := B.submatrix i₀.succAbove j.succAbove
        let R' : Set (Fin n) := {t | i₀.succAbove t ∈ R}
        have h1C : ∀ t b, C t b = 0 ∨ C t b = 1 ∨ C t b = -1 := by
          intro t b
          simpa [C, Matrix.submatrix_apply] using h1B (i₀.succAbove t) (j.succAbove b)
        have h2C : ∀ b : Fin n,
            (Finset.univ.filter (fun t : Fin n => C t b ≠ 0)).card ≤ 2 := by
          intro b
          let T : Finset (Fin n) := Finset.univ.filter (fun t => C t b ≠ 0)
          have hTcard : T.card = (T.image i₀.succAbove).card :=
            (Finset.card_image_of_injective T Fin.succAbove_right_injective).symm
          have hsub : T.image i₀.succAbove ⊆ F (j.succAbove b) := by
            intro x hx
            rw [Finset.mem_image] at hx
            obtain ⟨t, ht, rfl⟩ := hx
            have ht' : C t b ≠ 0 := (Finset.mem_filter.mp ht).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              by simpa [C, Matrix.submatrix_apply] using ht'⟩
          calc T.card = (T.image i₀.succAbove).card := hTcard
            _ ≤ (F (j.succAbove b)).card := Finset.card_le_card hsub
            _ ≤ 2 := h2B (j.succAbove b)
        have h3C : ∀ b t t' : Fin n, t ≠ t' → 0 < C t b * C t' b →
            (t ∈ R' ↔ t' ∉ R') := by
          intro b t t' hne hpos
          have hne' : i₀.succAbove t ≠ i₀.succAbove t' :=
            fun h => hne (Fin.succAbove_right_injective h)
          have hpos' :
              0 < B (i₀.succAbove t) (j.succAbove b) * B (i₀.succAbove t') (j.succAbove b) := by
            simpa [C, Matrix.submatrix_apply] using hpos
          have hR := h3B (j.succAbove b) (i₀.succAbove t) (i₀.succAbove t') hne' hpos'
          simpa [R'] using hR
        have h4C : ∀ b t t' : Fin n, t ≠ t' → C t b * C t' b < 0 →
            (t ∈ R' ↔ t' ∈ R') := by
          intro b t t' hne hneg
          have hne' : i₀.succAbove t ≠ i₀.succAbove t' :=
            fun h => hne (Fin.succAbove_right_injective h)
          have hneg' :
              B (i₀.succAbove t) (j.succAbove b) * B (i₀.succAbove t') (j.succAbove b) < 0 := by
            simpa [C, Matrix.submatrix_apply] using hneg
          have hR := h4B (j.succAbove b) (i₀.succAbove t) (i₀.succAbove t') hne' hneg'
          simpa [R'] using hR
        have hCmem := ih n (by omega) C R' h1C h2C h3C h4C
        exact sign_mul_mem (sign_mul_mem (neg_one_pow_mem _) (sign_mem_of_tri _ (h1B i₀ j))) hCmem

theorem solution {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (A : Matrix m n ℝ) (R₁ : Set m)
    (h1 : ∀ i j, A i j = 0 ∨ A i j = 1 ∨ A i j = -1)
    (h2 : ∀ j, (Finset.univ.filter (fun i => A i j ≠ 0)).card ≤ 2)
    (h3 : ∀ j i i', i ≠ i' → 0 < A i j * A i' j → (i ∈ R₁ ↔ i' ∉ R₁))
    (h4 : ∀ j i i', i ≠ i' → A i j * A i' j < 0 → (i ∈ R₁ ↔ i' ∈ R₁)) :
    A.IsTotallyUnimodular := by
  classical
  intro k f g hf hg
  let R : Set (Fin k) := {i | f i ∈ R₁}
  have h1' : ∀ i j : Fin k,
      (A.submatrix f g) i j = 0 ∨ (A.submatrix f g) i j = 1 ∨ (A.submatrix f g) i j = -1 := by
    intro i j
    simpa [Matrix.submatrix_apply] using h1 (f i) (g j)
  have h2' : ∀ j : Fin k,
      (Finset.univ.filter (fun i : Fin k => (A.submatrix f g) i j ≠ 0)).card ≤ 2 := by
    intro j
    have hcard :
        (Finset.univ.filter (fun i : Fin k => (A.submatrix f g) i j ≠ 0)).card
          = ((Finset.univ.filter (fun i : Fin k =>
              (A.submatrix f g) i j ≠ 0)).image f).card :=
      (Finset.card_image_of_injective _ hf).symm
    have hsub : (Finset.univ.filter (fun i : Fin k =>
          (A.submatrix f g) i j ≠ 0)).image f ⊆
        Finset.univ.filter (fun i : m => A i (g j) ≠ 0) := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      have ht' : (A.submatrix f g) t j ≠ 0 := (Finset.mem_filter.mp ht).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        by simpa [Matrix.submatrix_apply] using ht'⟩
    calc (Finset.univ.filter (fun i : Fin k => (A.submatrix f g) i j ≠ 0)).card
        = ((Finset.univ.filter (fun i : Fin k => (A.submatrix f g) i j ≠ 0)).image f).card :=
          hcard
      _ ≤ (Finset.univ.filter (fun i : m => A i (g j) ≠ 0)).card := Finset.card_le_card hsub
      _ ≤ 2 := h2 (g j)
  have h3' : ∀ j i i' : Fin k, i ≠ i' →
      0 < (A.submatrix f g) i j * (A.submatrix f g) i' j → (i ∈ R ↔ i' ∉ R) := by
    intro j i i' hne hpos
    have hne' : f i ≠ f i' := fun h => hne (hf h)
    have hpos' : 0 < A (f i) (g j) * A (f i') (g j) := by
      simpa [Matrix.submatrix_apply] using hpos
    have hR := h3 (g j) (f i) (f i') hne' hpos'
    simpa [R] using hR
  have h4' : ∀ j i i' : Fin k, i ≠ i' →
      (A.submatrix f g) i j * (A.submatrix f g) i' j < 0 → (i ∈ R ↔ i' ∈ R) := by
    intro j i i' hne hneg
    have hne' : f i ≠ f i' := fun h => hne (hf h)
    have hneg' : A (f i) (g j) * A (f i') (g j) < 0 := by
      simpa [Matrix.submatrix_apply] using hneg
    have hR := h4 (g j) (f i) (f i') hne' hneg'
    simpa [R] using hR
  exact tu_aux k (A.submatrix f g) R h1' h2' h3' h4'
