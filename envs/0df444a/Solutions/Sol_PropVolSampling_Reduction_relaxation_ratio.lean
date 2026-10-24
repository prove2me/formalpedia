-- Prove2me | solution 1 for PropVolSampling.Reduction.relaxation_ratio
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:03:17.370719+00:00
-- url     : https://prove2.me/submissions/89392ebd-6ea6-411c-b68a-fecf4178166d

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model
import Theorems.Thm_PropVolSampling_Reduction_lemma_2_1
import Theorems.Thm_PropVolSampling_Reduction_identity_4
import Theorems.Thm_PropVolSampling_Reduction_identity_6

namespace PropVolSampling.Reduction.WeightedRatioProof
open Matrix Finset

noncomputable def weightedMatrix {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ) :
    Matrix (Fin d) (Fin n) ℝ := fun a i => Real.sqrt (x i) * V a i

lemma weightedGram_eq {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    weightedGram V x = weightedMatrix V x * (weightedMatrix V x)ᵀ := by
  ext a b
  simp only [weightedGram, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply, weightedMatrix]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (Real.sqrt (x i) * V a i) * (Real.sqrt (x i) * V b i) =
      Real.sqrt (x i) ^ 2 * (V a i * V b i) by ring, Real.sq_sqrt (hx i)]

lemma colSub_weightedMatrix {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (x : Fin n → ℝ) (T : Finset (Fin n)) :
    colSub (weightedMatrix V x) T = colSubW V x T := rfl

lemma coeff_charpoly {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℝ) (hM : M.IsHermitian) (k : ℕ) (hk : k ≤ Fintype.card m) :
    M.charpoly.coeff (Fintype.card m-k) = (-1:ℝ)^k * Ek k M := by
  have h := Polynomial.coeff_eq_esymm_roots_of_splits hM.splits_charpoly
    (show Fintype.card m-k ≤ M.charpoly.natDegree by
      rw [Matrix.charpoly_natDegree_eq_dim]; omega)
  simpa only [Matrix.charpoly_natDegree_eq_dim, (Matrix.charpoly_monic M).leadingCoeff,
    one_mul, Nat.sub_sub_self hk, Ek] using h


lemma Ek_card_eq_det {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix m m ℝ) (hM : M.IsHermitian) : Ek (Fintype.card m) M = M.det := by
  have h := coeff_charpoly M hM (Fintype.card m) le_rfl
  simp only [Nat.sub_self] at h
  rw [Matrix.det_eq_sign_charpoly_coeff, h, ← mul_assoc, ← mul_pow]
  simp

lemma weighted_Ek {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (k : ℕ) (hk : k ≤ d) :
    Ek k (weightedGram V x) =
      ∑ T ∈ powersetCard k (univ : Finset (Fin n)),
        ((colSub V T)ᵀ * colSub V T).det * xPow x T := by
  rw [weightedGram_eq V x hx, (identity_4 (weightedMatrix V x) k).1,
    (identity_4 (weightedMatrix V x) k).2]
  apply Finset.sum_congr rfl
  intro T hT
  rw [colSub_weightedMatrix, lemma_2_1 V x hx T (by
    have hc := (Finset.mem_powersetCard.mp hT).2
    omega)]
  exact mul_comm _ _

lemma weighted_det_eq_sum {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hM : (weightedGram V x).IsHermitian) :
    (weightedGram V x).det =
      ∑ R ∈ powersetCard d (univ : Finset (Fin n)),
        ((colSub V R)ᵀ * colSub V R).det * xPow x R := by
  calc
    _ = Ek d (weightedGram V x) := by simpa only [Fintype.card_fin] using (Ek_card_eq_det _ hM).symm
    _ = _ := weighted_Ek V x hx d le_rfl

end PropVolSampling.Reduction.WeightedRatioProof

open Matrix Finset PropVolSampling.Reduction PropVolSampling.Reduction.WeightedRatioProof

theorem solution {d n : ℕ} (hd : 1 ≤ d) (V : Matrix (Fin d) (Fin n) ℝ) (x : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hpd : (weightedGram V x).PosDef) :
    aObj (weightedGram V x) =
      (∑ T ∈ powersetCard (d - 1) (univ : Finset (Fin n)),
          ((colSub V T)ᵀ * colSub V T).det * xPow x T) /
        (∑ R ∈ powersetCard d (univ : Finset (Fin n)),
          ((colSub V R)ᵀ * colSub V R).det * xPow x R) := by
  rw [identity_6 hd (weightedGram V x) hpd.isHermitian (ne_of_gt hpd.det_pos),
    weighted_Ek V x hx (d-1) (Nat.sub_le _ _), weighted_det_eq_sum V x hx hpd.isHermitian]
