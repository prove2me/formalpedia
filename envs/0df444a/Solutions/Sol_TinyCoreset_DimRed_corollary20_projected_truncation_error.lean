-- Prove2me | solution 1 for TinyCoreset.DimRed.corollary20_projected_truncation_error
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:05:22.992345+00:00
-- url     : https://prove2.me/submissions/7bd1ea01-8f80-4d44-8ef6-b571eef5b0db

import Theorems.Thm_TinyCoreset_DimRed_sec3_subspace_cost_lower_bound
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

private theorem frob_orthogonal_left {a b c : ℕ} (U : Matrix (Fin a) (Fin c) ℝ)
    (hU : Uᵀ * U = 1) (B : Matrix (Fin c) (Fin b) ℝ) :
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

private theorem frob_orthogonal_right {a b c : ℕ} (V : Matrix (Fin b) (Fin c) ℝ)
    (hV : Vᵀ * V = 1) (B : Matrix (Fin a) (Fin c) ℝ) :
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
open ProjLikeRetr.FixedRank

private theorem svd_threshold {n d : ℕ} {A : Matrix (Fin n) (Fin d) ℝ}
    {U : Matrix (Fin n) (Fin n) ℝ} {S : Matrix (Fin n) (Fin d) ℝ} {V : Matrix (Fin d) (Fin d) ℝ}
    (hA : IsSVD A U S V) (j : ℕ) (hj1 : 1 ≤ j) (ε : ℝ) (hε : 0 < ε) (m : ℕ)
    (hm : ⌈(j : ℝ) / ε⌉₊ + j ≤ m + 1) (hmnd : m + 1 ≤ min n d)
    (Y : Matrix (Fin d) (Fin (d - j)) ℝ) (hY : Yᵀ * Y = 1) :
    1 ≤ m ∧ (j : ℝ) * sigma S (m + 1) ^ 2 ≤ ε * frobSq (A * Y) := by
  have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hceilpos := Nat.ceil_pos.mpr (div_pos hjpos hε)
  have hmin : j + 1 ≤ min n d := by omega
  have hm₀ : 1 ≤ m := by omega
  have hjm : j ≤ m + 1 := by omega
  have hcount : (j : ℝ) ≤ ε * ((m + 1 - j : ℕ) : ℝ) := by
    have hceil : (j : ℝ) / ε ≤ (⌈(j : ℝ) / ε⌉₊ : ℝ) := Nat.le_ceil _
    have hnat : ⌈(j : ℝ) / ε⌉₊ ≤ m + 1 - j := by omega
    have hcast : (⌈(j : ℝ) / ε⌉₊ : ℝ) ≤ ((m + 1 - j : ℕ) : ℝ) := by exact_mod_cast hnat
    simpa only [mul_comm] using (div_le_iff₀ hε).mp (hceil.trans hcast)
  have hmono (i : ℕ) (hi : i ∈ Finset.Icc (j + 1) (m + 1)) :
      sigma S (m + 1) ^ 2 ≤ sigma S i ^ 2 := by
    have ⟨hi₁, hi₂⟩ := Finset.mem_Icc.mp hi
    have hσ₁ : 1 ≤ m + 1 ∧ m + 1 ≤ min n d := ⟨by omega, hmnd⟩
    have hσ₂ : 1 ≤ i ∧ i ≤ min n d := ⟨by omega, hi₂.trans hmnd⟩
    rw [sigma, dif_pos hσ₁, sigma, dif_pos hσ₂]
    apply (sq_le_sq₀ (hA.2.2.2.1 _ _ rfl) (hA.2.2.2.1 _ _ rfl)).2
    exact hA.2.2.2.2.1 _ _ _ _ rfl rfl (by change i - 1 ≤ m + 1 - 1; omega)
  have hcost := TinyCoreset.DimRed.sec3_subspace_cost_lower_bound A U S V hA j hj1 hmin Y hY
  have htail : ((m + 1 - j : ℕ) : ℝ) * sigma S (m + 1) ^ 2 ≤ frobSq (A * Y) := by
    calc
      _ = ∑ _i ∈ Finset.Icc (j + 1) (m + 1), sigma S (m + 1) ^ 2 := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        have hc : m + 1 + 1 - (j + 1) = m + 1 - j := by omega
        rw [hc]
      _ ≤ ∑ i ∈ Finset.Icc (j + 1) (m + 1), sigma S i ^ 2 := Finset.sum_le_sum hmono
      _ ≤ ∑ i ∈ Finset.Icc (j + 1) (min n d), sigma S i ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => sq_nonneg _)
        intro i hi
        have h := Finset.mem_Icc.mp hi
        exact Finset.mem_Icc.mpr ⟨h.1, h.2.trans hmnd⟩
      _ ≤ _ := hcost
  refine ⟨hm₀, ?_⟩
  calc
    _ ≤ (ε * ((m + 1 - j : ℕ) : ℝ)) * sigma S (m + 1) ^ 2 := mul_le_mul_of_nonneg_right hcount (sq_nonneg _)
    _ = ε * (((m + 1 - j : ℕ) : ℝ) * sigma S (m + 1) ^ 2) := mul_assoc _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left htail hε.le

theorem solution {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ)
    (U : Matrix (Fin n) (Fin n) ℝ) (S : Matrix (Fin n) (Fin d) ℝ)
    (V : Matrix (Fin d) (Fin d) ℝ) (hA : ProjLikeRetr.FixedRank.IsSVD A U S V)
    (j : ℕ) (hj1 : 1 ≤ j) (hjd : j + 1 ≤ d)
    (ε : ℝ) (hε : 0 < ε) (m : ℕ)
    (hm : ⌈(j : ℝ) / ε⌉₊ + j ≤ m + 1) (hmnd : m + 1 ≤ min n d)
    (X : Matrix (Fin d) (Fin j) ℝ) (Y : Matrix (Fin d) (Fin (d - j)) ℝ)
    (hX : Xᵀ * X = 1) (hY : Yᵀ * Y = 1) (hXY : Xᵀ * Y = 0) :
    0 ≤ frobSq (A * X * Xᵀ - ProjLikeRetr.FixedRank.truncSVD m U S V * X * Xᵀ) ∧
    frobSq (A * X * Xᵀ - ProjLikeRetr.FixedRank.truncSVD m U S V * X * Xᵀ) ≤
      ε * frobSq (A * Y) := by
  let R := S - truncate m S
  let B := Vᵀ * X
  have hU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp hA.1
  have hV : V * Vᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (n := Fin d) (R := ℝ)).mp hA.2.1
  have hB : Bᵀ * B = 1 := by
    dsimp [B]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc V Vᵀ X, hV, Matrix.one_mul, hX]
  have hdiagR (i : Fin n) (l : Fin d) (h : (i : ℕ) ≠ (l : ℕ)) : R i l = 0 := by
    dsimp only [R, Matrix.sub_apply]
    rw [hA.2.2.1 i l h, truncate_diagonal m S i l h, sub_zero]
  have hequal : frobSq (A * X * Xᵀ - truncSVD m U S V * X * Xᵀ) = frobSq (R * B) := by
    rw [← Matrix.sub_mul, ← Matrix.sub_mul, frob_orthogonal_right X hX, hA.2.2.2.2.2]
    change frobSq ((U * S * Vᵀ - U * truncate m S * Vᵀ) * X) = _
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_assoc (U * R) Vᵀ X,
      Matrix.mul_assoc U R B, frob_orthogonal_left U hU]
  have hweight : (∑ i : Fin d, ∑ l : Fin j, B i l ^ 2) = (j : ℝ) := by
    change frobSq B = _
    rw [frob_trace, hB, Matrix.trace_one, Fintype.card_fin]
  obtain ⟨_, threshold⟩ := svd_threshold hA j hj1 ε hε m hm hmnd Y hY
  rw [hequal]
  refine ⟨Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)), ?_⟩
  refine le_trans ?_ threshold
  rw [energy_diagonal R hdiagR]
  calc
    _ ≤ ∑ i : Fin d, sigma S (m + 1) ^ 2 * ∑ l : Fin j, B i l ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      dsimp only [R]
      rw [entries_sub, entries_truncate]
      by_cases hi : (i : ℕ) < m
      · simpa only [if_pos hi, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)] using
          sq_nonneg (sigma S (m + 1))
      · simpa only [if_neg hi, sub_zero] using tail_entry_le hA m hmnd i (le_of_not_gt hi)
    _ = _ := by rw [← Finset.mul_sum, hweight, mul_comm]
