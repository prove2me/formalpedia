-- Prove2me | solution 1 for StochLinOpt.UpperBound.det_designMatrix_succ
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T05:49:40.899592+00:00
-- url     : https://prove2.me/submissions/652fe622-681f-470d-b876-ab2832bd38a1

import Mathlib
import Definitions.Def_StochLinOpt_UpperBound_analysisQuantities

open Matrix
open StochLinOpt.UpperBound

private theorem rk1p {n : ℕ} (z v : Fin n → ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.vecMulVec z v).det = 1 + v ⬝ᵥ z := by
  rw [Matrix.vecMulVec_eq (Fin 1)]
  exact Matrix.det_one_add_replicateCol_mul_replicateRow z v

/-- The matrix determinant lemma, rank-one update form. -/
private theorem det_update {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (w : Fin n → ℝ) :
    (A + Matrix.vecMulVec w w).det = A.det * (1 + w ⬝ᵥ (A⁻¹ *ᵥ w)) := by
  have h1 : ∀ (B : Matrix (Fin n) (Fin n) ℝ) (v z : Fin n → ℝ),
      B * Matrix.vecMulVec v z = Matrix.vecMulVec (B *ᵥ v) z := by
    intro B v z
    ext i j
    simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct,
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have h2 : A *ᵥ (A⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]
  have hz : A * Matrix.vecMulVec (A⁻¹ *ᵥ w) w = Matrix.vecMulVec w w := by
    rw [h1, h2]
  have hfac : A + Matrix.vecMulVec w w = A * (1 + Matrix.vecMulVec (A⁻¹ *ᵥ w) w) := by
    rw [Matrix.mul_add, Matrix.mul_one, hz]
  rw [hfac, Matrix.det_mul, rk1p]

/-- The design matrix `A_t = I + ∑_{τ<t} x_τ x_τᵀ` is positive definite. -/
private theorem dm_pd {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) : (designMatrix x t).PosDef := by
  have hpsd : ∀ v : Fin n → ℝ, (Matrix.vecMulVec v v).PosSemidef := fun v => by
    simpa using Matrix.posSemidef_vecMulVec_self_star v
  have hsumpsd : (∑ τ ∈ Finset.Ico 1 t, Matrix.vecMulVec (x τ) (x τ)).PosSemidef :=
    Matrix.posSemidef_sum _ (fun i _ => hpsd _)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [designMatrix]
    exact Matrix.IsHermitian.add (by simp [Matrix.IsHermitian]) hsumpsd.1
  · intro y hy
    have h1 : (0:ℝ) ≤ star y ⬝ᵥ ((∑ τ ∈ Finset.Ico 1 t, Matrix.vecMulVec (x τ) (x τ)) *ᵥ y) :=
      hsumpsd.dotProduct_mulVec_nonneg y
    have h2 : (0:ℝ) < star y ⬝ᵥ ((1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) := by
      rw [Matrix.one_mulVec]
      simp only [star_trivial]
      rcases Function.ne_iff.mp hy with ⟨i, hi⟩
      exact Finset.sum_pos' (fun j _ => mul_self_nonneg _)
        ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
    rw [designMatrix, Matrix.add_mulVec, dotProduct_add]
    linarith

private theorem dm_det_pos {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) : 0 < (designMatrix x t).det :=
  (dm_pd x t).det_pos

private theorem dm_unit {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) : IsUnit (designMatrix x t).det :=
  isUnit_iff_ne_zero.mpr (dm_det_pos x t).ne'

private theorem dm_rec {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    designMatrix x (t + 1) = designMatrix x t + Matrix.vecMulVec (x t) (x t) := by
  rw [designMatrix, designMatrix, Finset.sum_Ico_succ_top ht]
  abel

/-- `w_t² = x_tᵀ A_t⁻¹ x_t` (the argument of the square root is nonnegative). -/
private theorem width_sq {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) :
    width x t ^ 2 = x t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ x t) := by
  have hpd : ((designMatrix x t)⁻¹).PosDef := Matrix.posDef_inv_iff.mpr (dm_pd x t)
  have hnn : (0:ℝ) ≤ x t ⬝ᵥ ((designMatrix x t)⁻¹ *ᵥ x t) := by
    simpa using hpd.posSemidef.dotProduct_mulVec_nonneg (x t)
  rw [width, Real.sq_sqrt hnn]

/-- The determinant of `A_{t+1}` telescopes into the widths. -/
private theorem det_dm_succ {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) :
    (designMatrix x (t + 1)).det = ∏ τ ∈ Finset.Icc 1 t, (1 + width x τ ^ 2) := by
  induction t with
  | zero =>
    simp [designMatrix]
  | succ s ih =>
    rw [dm_rec x (s + 1) (by omega), det_update _ (dm_unit x (s + 1)),
      Finset.prod_Icc_succ_top (by omega : 1 ≤ s + 1), ih, width_sq]

theorem solution {n : ℕ} (x : ℕ → Fin n → ℝ) (t : ℕ) :
    (designMatrix x (t + 1)).det = ∏ τ ∈ Finset.Icc 1 t, (1 + width x τ ^ 2) :=
  det_dm_succ x t
