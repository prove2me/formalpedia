-- Prove2me | solution 1 for TinyCoreset.DimRed.sec3_subspace_cost_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @DavidDenisov
-- created : 2026-11-27T00:01:37.80193+00:00
-- url     : https://prove2.me/submissions/70f56914-edff-4223-bd6b-f255600ed831

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
    (j : ℕ) (hj1 : 1 ≤ j) (hjnd : j + 1 ≤ min n d)
    (Y : Matrix (Fin d) (Fin (d - j)) ℝ) (hY : Yᵀ * Y = 1) :
    (∑ i ∈ Finset.Icc (j + 1) (min n d), sigma S i ^ 2) ≤ frobSq (A * Y) := by
  classical
  let B := Vᵀ * Y
  let w (i : Fin d) : ℝ := ∑ l : Fin (d - j), B i l ^ 2
  let tail (i : Fin d) : ℝ := if j ≤ (i : ℕ) then 1 else 0
  let τ : ℝ := sigma S (j + 1) ^ 2
  have hU : Uᵀ * U = 1 := (Matrix.mem_orthogonalGroup_iff' (n := Fin n) (R := ℝ)).mp hA.1
  have hV : V * Vᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (n := Fin d) (R := ℝ)).mp hA.2.1
  have hB : Bᵀ * B = 1 := by
    dsimp [B]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc V Vᵀ Y, hV, Matrix.one_mul, hY]
  have energy : frobSq (A * Y) = ∑ i, entries S i ^ 2 * w i := by
    rw [hA.2.2.2.2.2, Matrix.mul_assoc (U * S) Vᵀ Y, Matrix.mul_assoc U S B,
      frob_orthogonal_left U hU, energy_diagonal S hA.2.2.1]
  have weight_sum : (∑ i, w i) = ((d - j : ℕ) : ℝ) := by
    change frobSq B = _
    rw [frob_trace, hB, Matrix.trace_one, Fintype.card_fin]
  have tail_card : (Finset.univ.filter (fun i : Fin d => j ≤ (i : ℕ))).card = d - j := by
    rw [← Fintype.card_fin (d - j), ← Finset.card_univ]
    refine Finset.card_bij (fun i hi => (⟨(i : ℕ) - j, ?_⟩ : Fin (d - j)))
      (fun _ _ => Finset.mem_univ _) ?_ ?_
    · have hle := (Finset.mem_filter.mp hi).2
      omega
    · intro i hi l hl eq
      apply Fin.ext
      have eq' : (i : ℕ) - j = (l : ℕ) - j := congrArg Fin.val eq
      have hi' := (Finset.mem_filter.mp hi).2
      have hl' := (Finset.mem_filter.mp hl).2
      omega
    · intro l _
      have h : j + (l : ℕ) < d := by omega
      refine ⟨⟨j + (l : ℕ), h⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · change j ≤ j + (l : ℕ)
        omega
      apply Fin.ext
      simp
  have tail_sum : (∑ i, tail i) = ((d - j : ℕ) : ℝ) := by
    dsimp only [tail]
    rw [← Finset.sum_filter, Finset.sum_const, tail_card, nsmul_eq_mul, mul_one]
  have hn : j < n := by omega
  have hd : j < d := by omega
  have threshold : sigma S (j + 1) = S ⟨j, hn⟩ ⟨j, hd⟩ := by simp [sigma, hjnd]
  have ordered_prefix (i : Fin d) (hi : (i : ℕ) < j) : τ ≤ entries S i ^ 2 := by
    have hi' : (i : ℕ) < n := by omega
    dsimp only [τ]
    rw [threshold, entries, dif_pos hi']
    apply (sq_le_sq₀ (hA.2.2.2.1 _ _ rfl) (hA.2.2.2.1 _ _ rfl)).2
    exact hA.2.2.2.2.1 _ _ _ _ rfl rfl hi.le
  have pointwise (i : Fin d) : (entries S i ^ 2 - τ) * (w i - tail i) ≥ 0 := by
    by_cases hi : (i : ℕ) < j
    · simp only [tail, if_neg (Nat.not_le_of_gt hi), sub_zero]
      exact mul_nonneg (sub_nonneg.mpr (ordered_prefix i hi)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    · have hi' := Nat.le_of_not_gt hi
      simp only [tail, if_pos hi']
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (tail_entry_le hA j hjnd i hi'))
        (sub_nonpos.mpr (weight_le_one B hB i))
  have dominance : (∑ i, entries S i ^ 2 * tail i) ≤ ∑ i, entries S i ^ 2 * w i := by
    have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ => pointwise i)
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, weight_sum, tail_sum] at hsum
    linarith
  have tail_energy : (∑ i, entries S i ^ 2 * tail i) = ∑ i ∈ Finset.Icc (j + 1) (min n d), sigma S i ^ 2 := by
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i : Fin d => j ≤ (i : ℕ) ∧ (i : ℕ) < n), entries S i ^ 2 := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hn : (i : ℕ) < n <;> by_cases hj : j ≤ (i : ℕ)
        all_goals simp [tail, entries, hn, hj]
      _ = _ := by
        refine Finset.sum_bij (fun i _ => (i : ℕ) + 1) ?_ ?_ ?_ ?_
        · intro i hi
          have ⟨hji, hni⟩ := (Finset.mem_filter.mp hi).2
          exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        · intro i _ l _ eq
          exact Fin.ext (by omega)
        · intro r hr
          have ⟨hr₁, hr₂⟩ := Finset.mem_Icc.mp hr
          refine ⟨⟨r - 1, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · change j ≤ r - 1 ∧ r - 1 < n
            omega
          · change r - 1 + 1 = r
            omega
        · intro i hi
          have hni := (Finset.mem_filter.mp hi).2.2
          have hmin : (i : ℕ) + 1 ≤ min n d := by omega
          simp [entries, sigma, hni, hmin]
  rw [← tail_energy, energy]
  exact dominance
