-- Prove2me | solution 1 for TinyCoreset.DimRed.lemma14_projection_gap
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-26T23:57:11.603998+00:00
-- url     : https://prove2.me/submissions/c53ec6db-b86a-4056-a664-3f35b9d96d5f

import Mathlib
import Definitions.Def_ProjLikeRetr_FixedRank_SVD
import Definitions.Def_TinyCoreset_DimRed_Setting

set_option autoImplicit false

open TinyCoreset
open TinyCoreset.DimRed

open scoped Matrix

open ProjLikeRetr.FixedRank

private theorem frob_trace {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    frobSq B = (Bᵀ * B).trace := by
  simp only [frobSq, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  exact Finset.sum_comm

private theorem frob_orthogonal_left {a b : ℕ} (U : Matrix (Fin a) (Fin a) ℝ)
    (hU : Uᵀ * U = 1) (B : Matrix (Fin a) (Fin b) ℝ) :
    frobSq (U * B) = frobSq B := by
  rw [frob_trace, frob_trace, Matrix.transpose_mul, Matrix.mul_assoc Bᵀ Uᵀ (U * B),
    ← Matrix.mul_assoc Uᵀ U B, hU, Matrix.one_mul]

private def entries {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ) (i : Fin d) : ℝ :=
  if hi : (i : ℕ) < n then D ⟨i, hi⟩ i else 0

private theorem diag_gram {n d : ℕ} (D : Matrix (Fin n) (Fin d) ℝ)
    (hD : ∀ (i : Fin n) (j : Fin d), (i : ℕ) ≠ (j : ℕ) → D i j = 0) :
    Dᵀ * D = Matrix.diagonal (fun i => entries D i ^ 2) := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq]
    by_cases hi : (i : ℕ) < n
    · rw [entries, dif_pos hi, Finset.sum_eq_single (⟨i, hi⟩ : Fin n)]
      · ring
      · intro k _ hk
        have hneq : (k : ℕ) ≠ (i : ℕ) := fun h => hk (Fin.ext h)
        rw [hD k i hneq, zero_mul]
      · simp
    · rw [entries, dif_neg hi, zero_pow (by decide : (2 : ℕ) ≠ 0)]
      apply Finset.sum_eq_zero
      intro k _
      have hneq : (k : ℕ) ≠ (i : ℕ) := by omega
      rw [hD k i hneq, zero_mul]
  · rw [Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : (k : ℕ) = (i : ℕ)
    · have hneq : (k : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext (hk.symm.trans h))
      rw [hD k j hneq, mul_zero]
    · rw [hD k i hk, zero_mul]

private theorem energy_diagonal {n d j : ℕ} (D : Matrix (Fin n) (Fin d) ℝ)
    (hD : ∀ (i : Fin n) (l : Fin d), (i : ℕ) ≠ (l : ℕ) → D i l = 0)
    (B : Matrix (Fin d) (Fin j) ℝ) :
    frobSq (D * B) = ∑ i : Fin d, entries D i ^ 2 * ∑ l : Fin j, B i l ^ 2 := by
  rw [frob_trace, Matrix.transpose_mul, Matrix.mul_assoc Bᵀ Dᵀ (D * B),
    ← Matrix.mul_assoc Dᵀ D B, Matrix.trace_mul_comm Bᵀ,
    Matrix.mul_assoc (Dᵀ * D) B Bᵀ, diag_gram D hD]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two]

private def truncate {n d : ℕ} (m : ℕ) (S : Matrix (Fin n) (Fin d) ℝ) : Matrix (Fin n) (Fin d) ℝ :=
  Matrix.of (fun i j => if i.val = j.val ∧ i.val < m then S i j else 0)

private theorem truncate_diagonal {n d : ℕ} (m : ℕ) (S : Matrix (Fin n) (Fin d) ℝ) :
    ∀ (i : Fin n) (j : Fin d), (i : ℕ) ≠ (j : ℕ) → truncate m S i j = 0 := by
  intro i j hij
  simp [truncate, hij]

private theorem entries_truncate {n d : ℕ} (m : ℕ) (S : Matrix (Fin n) (Fin d) ℝ) (i : Fin d) :
    entries (truncate m S) i = if (i : ℕ) < m then entries S i else 0 := by
  by_cases hi : (i : ℕ) < n <;> simp [entries, hi, truncate]

private theorem tail_entry_le {n d : ℕ} {A U S V} (hA : IsSVD (n := n) (m := d) A U S V)
    (m : ℕ) (hm : m + 1 ≤ min n d) (i : Fin d) (hi : m ≤ (i : ℕ)) :
    entries S i ^ 2 ≤ sigma S (m + 1) ^ 2 := by
  have hmn : m < n := by omega
  have hmd : m < d := by omega
  by_cases hin : (i : ℕ) < n
  · rw [entries, dif_pos hin]
    have hs : sigma S (m + 1) = S ⟨m, hmn⟩ ⟨m, hmd⟩ := by
      simp [sigma, hm]
    rw [hs]
    apply sq_le_sq₀ (hA.2.2.2.1 _ _ rfl) (hA.2.2.2.1 _ _ rfl) |>.2
    exact hA.2.2.2.2.1 _ _ _ _ rfl rfl hi
  · simp [entries, hin, sq_nonneg]

theorem solution {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (hA : ProjLikeRetr.FixedRank.IsSVD A U S V)
    (j : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d)
    (X : Matrix (Fin d) (Fin j) ℝ) (hX : Xᵀ * X = 1)
    (m : ℕ) (hm1 : 1 ≤ m) (hmnd : m + 1 ≤ min n d) :
    0 ≤ frobSq (A * X) - frobSq (ProjLikeRetr.FixedRank.truncSVD m U S V * X) ∧
    frobSq (A * X) - frobSq (ProjLikeRetr.FixedRank.truncSVD m U S V * X) ≤
      (j : ℝ) * sigma S (m + 1) ^ 2 := by
  let B := Vᵀ * X
  have hU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp hA.1
  have hV : V * Vᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (n := Fin d) (R := ℝ)).mp hA.2.1
  have hB : Bᵀ * B = 1 := by
    dsimp [B]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc V Vᵀ X, hV, Matrix.one_mul, hX]
  have hfull : frobSq (A * X) = frobSq (S * B) := by
    rw [hA.2.2.2.2.2, Matrix.mul_assoc (U * S) Vᵀ X, Matrix.mul_assoc U S B,
      frob_orthogonal_left U hU]
  have hcut : frobSq (truncSVD m U S V * X) = frobSq (truncate m S * B) := by
    change frobSq ((U * truncate m S * Vᵀ) * X) = _
    rw [Matrix.mul_assoc (U * truncate m S) Vᵀ X, Matrix.mul_assoc U (truncate m S) B,
      frob_orthogonal_left U hU]
  rw [hfull, hcut, energy_diagonal S hA.2.2.1, energy_diagonal _ (truncate_diagonal m S),
    ← Finset.sum_sub_distrib]
  simp only [entries_truncate]
  let weight (i : Fin d) := ∑ l : Fin j, B i l ^ 2
  have weight_nonneg (i : Fin d) : 0 ≤ weight i := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsum : ∑ i, weight i = (j : ℝ) := by
    change frobSq B = _
    rw [frob_trace, hB, Matrix.trace_one, Fintype.card_fin]
  constructor
  · apply Finset.sum_nonneg
    intro i _
    change 0 ≤ entries S i ^ 2 * weight i - (if (i : ℕ) < m then entries S i else 0) ^ 2 * weight i
    split_ifs <;> simp [mul_nonneg (sq_nonneg _) (weight_nonneg i)]
  · calc
      _ ≤ ∑ i, sigma S (m + 1) ^ 2 * weight i := by
        apply Finset.sum_le_sum
        intro i _
        change entries S i ^ 2 * weight i - (if (i : ℕ) < m then entries S i else 0) ^ 2 * weight i ≤ _
        split_ifs with hi
        · simpa only [sub_self] using mul_nonneg (sq_nonneg (sigma S (m + 1))) (weight_nonneg i)
        · simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, sub_zero] using
            mul_le_mul_of_nonneg_right (tail_entry_le hA m hmnd i (le_of_not_gt hi)) (weight_nonneg i)
      _ = _ := by rw [← Finset.mul_sum, hsum, mul_comm]
