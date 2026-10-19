-- Prove2me | solution 1 for RobustSpecClust.Round.eq_G6
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-17T11:00:14.049297+00:00
-- url     : https://prove2.me/submissions/7700d746-25f7-4a88-b18f-1721c47ad00d

import Theorems.Thm_RobustSpecClust_Round_davis_kahan
import Theorems.Thm_RobustSpecClust_Round_U0_isTopEigvecs
import Theorems.Thm_RobustSpecClust_Round_frobSq_le_l1

open RobustSpecClust.Round Matrix

theorem solution {n r : ℕ} [NeZero r] (φ : Fin n → Fin r) (hφ : ∀ k, 0 < clusterSize φ k)
    (Xh : Matrix (Fin n) (Fin n) ℝ) (hsym : Xhᵀ = Xh) (hbox : ∀ i j, 0 ≤ Xh i j ∧ Xh i j ≤ 1)
    (Uh : Matrix (Fin n) (Fin r) ℝ) (hU : IsTopEigvecs Xh Uh)
    (O : Matrix (Fin r) (Fin r) ℝ) (hO : O ∈ Matrix.orthogonalGroup (Fin r) ℝ)
    (hOopt : ∀ O' ∈ Matrix.orthogonalGroup (Fin r) ℝ,
      frobSq (Uh - U0 φ * O) ≤ frobSq (Uh - U0 φ * O')) :
    frobSq (Uh - U0 φ * O) ≤ 8 * l1 (Xh - trueClust φ) / nmin φ ^ 2 := by
  obtain ⟨hX0, hker⟩ := U0_isTopEigvecs φ hφ
  -- `X⁰` is symmetric with entries in `{0,1}`
  have hX0sym : (trueClust φ)ᵀ = trueClust φ := by
    ext i j
    simp only [transpose_apply, trueClust, eq_comm]
  have hX0box : ∀ i j, 0 ≤ trueClust φ i j ∧ trueClust φ i j ≤ 1 := by
    intro i j
    simp only [trueClust]
    split_ifs <;> norm_num
  -- the eigengap of `X⁰` is `n_min`
  have hg : 0 < nmin φ := (Finset.lt_inf'_iff _).mpr fun k _ => Nat.cast_pos.mpr (hφ k)
  have hgap : ∀ v : Fin n → ℝ, (U0 φ)ᵀ *ᵥ v = 0 → ∀ k,
      v ⬝ᵥ (trueClust φ *ᵥ v) ≤ ((clusterSize φ k : ℝ) - nmin φ) * (v ⬝ᵥ v) := by
    intro v hv k
    rw [hker v hv, dotProduct_zero]
    have hk : nmin φ ≤ (clusterSize φ k : ℝ) := Finset.inf'_le _ (Finset.mem_univ k)
    exact mul_nonneg (by linarith) (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))
  -- Davis–Kahan
  obtain ⟨O', hO', hdk⟩ := davis_kahan (trueClust φ) Xh hX0sym hsym (U0 φ) Uh
    (fun k => (clusterSize φ k : ℝ)) hX0 (nmin φ) hg hgap hU
  have hfro0 : ∀ {m : ℕ} {p : ℕ} (M : Matrix (Fin m) (Fin p) ℝ), 0 ≤ frobSq M := fun M =>
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  -- square the Davis–Kahan bound: `‖U⁰ − ÛO'‖_F² ≤ 8‖X̂ − X⁰‖_F² / n_min²`
  have hc : ((2 : ℝ) ^ (3 / 2 : ℝ)) ^ 2 = 8 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [show (3 / 2 : ℝ) * ((2 : ℕ) : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have hdk2 : frobSq (U0 φ - Uh * O') ≤ 8 * frobSq (Xh - trueClust φ) / nmin φ ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) hdk 2
    rwa [Real.sq_sqrt (hfro0 _), div_pow, mul_pow, hc, Real.sq_sqrt (hfro0 _)] at h
  -- orthogonal invariance of the Frobenius norm
  have hst : star O' = O'ᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have h1 : O' * O'ᵀ = 1 := by
    rw [← hst]; exact (Matrix.mem_orthogonalGroup_iff (Fin r) ℝ).mp hO'
  have h2 : O'ᵀ * O' = 1 := by
    rw [← hst]; exact (Matrix.mem_orthogonalGroup_iff' (Fin r) ℝ).mp hO'
  have hOt : O'ᵀ ∈ Matrix.orthogonalGroup (Fin r) ℝ := by
    rw [Matrix.mem_orthogonalGroup_iff]
    simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial,
      transpose_transpose] using h2
  have htr : ∀ M : Matrix (Fin n) (Fin r) ℝ, frobSq M = trace (M * Mᵀ) := by
    intro M
    simp only [frobSq, trace, diag_apply, mul_apply, transpose_apply, sq]
  have hinv : ∀ M : Matrix (Fin n) (Fin r) ℝ, frobSq (M * O'ᵀ) = frobSq M := by
    intro M
    rw [htr, htr, transpose_mul, transpose_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc O'ᵀ,
      h2, Matrix.one_mul]
  have hneg : ∀ M : Matrix (Fin n) (Fin r) ℝ, frobSq (-M) = frobSq M := by
    intro M
    simp only [frobSq, Matrix.neg_apply, neg_sq]
  have hrot : frobSq (Uh - U0 φ * O'ᵀ) = frobSq (U0 φ - Uh * O') := by
    have : Uh - U0 φ * O'ᵀ = -((U0 φ - Uh * O') * O'ᵀ) := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, h1, Matrix.mul_one, neg_sub]
    rw [this, hneg, hinv]
  -- (iii): `‖X̂ − X⁰‖_F² ≤ ‖X̂ − X⁰‖₁`
  have hl1 := frobSq_le_l1 Xh (trueClust φ) hbox hX0box
  have hg2 : 0 < nmin φ ^ 2 := by positivity
  calc frobSq (Uh - U0 φ * O) ≤ frobSq (Uh - U0 φ * O'ᵀ) := hOopt _ hOt
    _ = frobSq (U0 φ - Uh * O') := hrot
    _ ≤ 8 * frobSq (Xh - trueClust φ) / nmin φ ^ 2 := hdk2
    _ ≤ 8 * l1 (Xh - trueClust φ) / nmin φ ^ 2 := by
        apply div_le_div_of_nonneg_right _ hg2.le
        linarith
