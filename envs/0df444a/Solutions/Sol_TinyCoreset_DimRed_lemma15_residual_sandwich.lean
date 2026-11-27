-- Prove2me | solution 1 for TinyCoreset.DimRed.lemma15_residual_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-26T23:58:30.662076+00:00
-- url     : https://prove2.me/submissions/b0ccba30-8862-4f88-beb0-9c8646066cab

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

private theorem frob_transpose {a b : ℕ} (B : Matrix (Fin a) (Fin b) ℝ) :
    frobSq Bᵀ = frobSq B := by
  simp only [frobSq, Matrix.transpose_apply]
  exact Finset.sum_comm

private theorem frob_orthogonal_right {a b : ℕ} (V : Matrix (Fin b) (Fin b) ℝ)
    (hV : Vᵀ * V = 1) (B : Matrix (Fin a) (Fin b) ℝ) :
    frobSq (B * Vᵀ) = frobSq B := by
  rw [← frob_transpose (B * Vᵀ), Matrix.transpose_mul, Matrix.transpose_transpose,
    frob_orthogonal_left V hV, frob_transpose]

private theorem weight_le_one {d j : ℕ} (B : Matrix (Fin d) (Fin j) ℝ) (hB : Bᵀ * B = 1)
    (i : Fin d) : ∑ l, B i l ^ 2 ≤ 1 := by
  let P := B * Bᵀ
  have hs (u v : Fin d) : P u v = P v u := by
    simp only [P, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hPP : P * P = P := by
    dsimp only [P]
    rw [Matrix.mul_assoc B Bᵀ (B * Bᵀ), ← Matrix.mul_assoc Bᵀ B Bᵀ, hB, Matrix.one_mul]
  have hx : P i i = ∑ l, B i l ^ 2 := by simp only [P, Matrix.mul_apply, Matrix.transpose_apply, pow_two]
  have hsquare : (P i i) ^ 2 ≤ P i i := by
    calc
      _ ≤ ∑ v, (P i v) ^ 2 := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      _ = (P * P) i i := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun v _ => by rw [← hs i v, pow_two]
      _ = _ := by rw [hPP]
  rw [← hx]
  by_contra! h
  nlinarith [mul_pos (sub_pos.mpr h) (show 0 < P i i by linarith)]

private theorem entries_sub {n d : ℕ} (S T : Matrix (Fin n) (Fin d) ℝ) (i : Fin d) :
    entries (S - T) i = entries S i - entries T i := by
  by_cases hi : (i : ℕ) < n <;> simp [entries, hi, Matrix.sub_apply]

theorem solution {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (hA : ProjLikeRetr.FixedRank.IsSVD A U S V)
    (j : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d)
    (m : ℕ) (hm1 : 1 ≤ m) (hmnd : m + 1 ≤ min n d)
    (Y : Matrix (Fin d) (Fin (d - j)) ℝ) (hY : Yᵀ * Y = 1) :
    0 ≤ (frobSq (ProjLikeRetr.FixedRank.truncSVD m U S V * Y) +
      frobSq (A - ProjLikeRetr.FixedRank.truncSVD m U S V)) - frobSq (A * Y) ∧
    (frobSq (ProjLikeRetr.FixedRank.truncSVD m U S V * Y) +
      frobSq (A - ProjLikeRetr.FixedRank.truncSVD m U S V)) - frobSq (A * Y) ≤
      (j : ℝ) * sigma S (m + 1) ^ 2 := by
  let B := Vᵀ * Y
  let T := truncate m S
  let R := S - T
  have hU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp hA.1
  have hV : V * Vᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (n := Fin d) (R := ℝ)).mp hA.2.1
  have hV' : Vᵀ * V = 1 := (Matrix.mem_orthogonalGroup_iff' (n := Fin d) (R := ℝ)).mp hA.2.1
  have hB : Bᵀ * B = 1 := by
    dsimp [B]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc V Vᵀ Y, hV, Matrix.one_mul, hY]
  have hfull : frobSq (A * Y) = frobSq (S * B) := by
    rw [hA.2.2.2.2.2, Matrix.mul_assoc (U * S) Vᵀ Y, Matrix.mul_assoc U S B,
      frob_orthogonal_left U hU]
  have hcut : frobSq (truncSVD m U S V * Y) = frobSq (T * B) := by
    change frobSq ((U * T * Vᵀ) * Y) = _
    rw [Matrix.mul_assoc (U * T) Vᵀ Y, Matrix.mul_assoc U T B, frob_orthogonal_left U hU]
  have hrest : frobSq (A - truncSVD m U S V) = frobSq R := by
    rw [hA.2.2.2.2.2]
    change frobSq (U * S * Vᵀ - U * T * Vᵀ) = _
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, frob_orthogonal_right V hV', frob_orthogonal_left U hU]
  have hdiagR (i : Fin n) (l : Fin d) (h : (i : ℕ) ≠ (l : ℕ)) : R i l = 0 := by
    dsimp only [R, T, Matrix.sub_apply]
    rw [hA.2.2.1 i l h, truncate_diagonal m S i l h, sub_zero]
  have energyR : frobSq R = ∑ i, entries R i ^ 2 := by
    have h := energy_diagonal R hdiagR (1 : Matrix (Fin d) (Fin d) ℝ)
    rw [Matrix.mul_one] at h
    convert h using 1
    apply Finset.sum_congr rfl
    intro i _
    simp [Matrix.one_apply]
  let weight (i : Fin d) := ∑ l : Fin (d - j), B i l ^ 2
  have weight_nonneg (i : Fin d) : 0 ≤ weight i := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have weight_le (i : Fin d) : weight i ≤ 1 := weight_le_one B hB i
  have weight_sum : (∑ i, weight i) = ((d - j : ℕ) : ℝ) := by
    change frobSq B = _
    rw [frob_trace, hB, Matrix.trace_one, Fintype.card_fin]
  have complement_sum : (∑ i, (1 - weight i)) = (j : ℝ) := by
    rw [Finset.sum_sub_distrib, weight_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_sub (by omega : j ≤ d)]
    ring
  have gap : (frobSq (truncSVD m U S V * Y) + frobSq (A - truncSVD m U S V)) -
      frobSq (A * Y) = ∑ i : Fin d, if m ≤ (i : ℕ) then entries S i ^ 2 * (1 - weight i) else 0 := by
    rw [hfull, hcut, hrest, energyR, energy_diagonal S hA.2.2.1, energy_diagonal T (truncate_diagonal m S),
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    change entries (truncate m S) i ^ 2 * weight i + entries (S - truncate m S) i ^ 2 -
      entries S i ^ 2 * weight i = _
    rw [entries_sub, entries_truncate]
    by_cases hi : (i : ℕ) < m
    · simp [hi, Nat.not_le_of_gt hi]
    · simp [hi, Nat.le_of_not_gt hi]
      ring
  rw [gap]
  constructor
  · apply Finset.sum_nonneg
    intro i _
    split_ifs
    · exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (weight_le i))
    · exact le_rfl
  · calc
      _ ≤ ∑ i, sigma S (m + 1) ^ 2 * (1 - weight i) := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi
        · exact mul_le_mul_of_nonneg_right (tail_entry_le hA m hmnd i hi) (sub_nonneg.mpr (weight_le i))
        · exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (weight_le i))
      _ = _ := by rw [← Finset.mul_sum, complement_sum, mul_comm]
