-- Prove2me | solution 1 for PropVolSampling.Reduction.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:54:22.217571+00:00
-- url     : https://prove2.me/submissions/7f800a96-8179-43a2-8daa-aba9b8d24eaf

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model

namespace PropVolSampling.Reduction.WeightedMinorProof
open Matrix Finset

lemma colSubW_eq_mul_diagonal {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (x : Fin n → ℝ) (T : Finset (Fin n)) :
    colSubW V x T = colSub V T * Matrix.diagonal (fun i : T => Real.sqrt (x i)) := by
  ext a i
  simp only [Matrix.mul_diagonal, colSubW, colSub, Matrix.submatrix_apply, id_eq]
  ring

lemma sqrt_product_sq {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (T : Finset (Fin n)) :
    (∏ i : T, Real.sqrt (x i)) ^ 2 = xPow x T := by
  rw [← Finset.prod_pow]
  simp only [Real.sq_sqrt (hx _), Finset.prod_coe_sort, xPow]

lemma weighted_minor {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (T : Finset (Fin n)) :
    ((colSubW V x T)ᵀ * colSubW V x T).det =
      xPow x T * ((colSub V T)ᵀ * colSub V T).det := by
  let D : Matrix T T ℝ := Matrix.diagonal (fun i : T => Real.sqrt (x i))
  have hg : (colSubW V x T)ᵀ * colSubW V x T = D * ((colSub V T)ᵀ * colSub V T) * D := by
    rw [colSubW_eq_mul_diagonal, Matrix.transpose_mul, Matrix.diagonal_transpose]
    simp only [D, Matrix.mul_assoc]
  rw [hg, Matrix.det_mul, Matrix.det_mul]
  have hdet : D.det ^ 2 = xPow x T := by
    simpa only [D, Matrix.det_diagonal] using sqrt_product_sq x hx T
  calc
    _ = D.det ^ 2 * ((colSub V T)ᵀ * colSub V T).det := by ring
    _ = _ := by rw [hdet]

end PropVolSampling.Reduction.WeightedMinorProof

open Matrix Finset PropVolSampling.Reduction

theorem solution {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i)
    (T : Finset (Fin n)) (_hT : T.card ≤ d) :
    ((colSubW V x T)ᵀ * colSubW V x T).det = xPow x T * ((colSub V T)ᵀ * colSub V T).det :=
  WeightedMinorProof.weighted_minor V x hx T
