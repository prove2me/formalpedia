-- Prove2me | solution 1 for PropVolSampling.Reduction.inequality_5
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:08:19.543792+00:00
-- url     : https://prove2.me/submissions/932fbaa1-5d37-4632-90a3-ef6ac73736d5

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model
import Theorems.Thm_PropVolSampling_Reduction_lemma_2_1
import Theorems.Thm_PropVolSampling_Reduction_identity_4
import Theorems.Thm_PropVolSampling_Reduction_identity_6
import Theorems.Thm_PropVolSampling_Reduction_expectation_ratio
import Theorems.Thm_PropVolSampling_Reduction_relaxation_ratio


noncomputable section Inline_VOL_Finite
open Matrix Finset
namespace PropVolSampling.Reduction.VOL7FiniteProof

lemma xPow_indicator {n : ℕ} (S T : Finset (Fin n)) :
    xPow (fun i => if i ∈ S then (1 : ℝ) else 0) T = if T ⊆ S then 1 else 0 := by
  classical
  by_cases h : T ⊆ S
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [h hi]
  · rw [if_neg h]
    obtain ⟨i, hi, hn⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (by simp [hn])

lemma sum_subset_swap {n : ℕ} (k : ℕ) (F μ : Finset (Fin n) → ℝ) :
    (∑ S, μ S * ∑ T ∈ S.powersetCard k, F T) =
      ∑ T ∈ (univ : Finset (Fin n)).powersetCard k, F T * prSup μ T := by
  classical
  have hsets (S : Finset (Fin n)) : S.powersetCard k =
      ((univ : Finset (Fin n)).powersetCard k).filter (fun T => T ⊆ S) := by
    ext T
    simp only [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ, true_and]
    tauto
  calc
    _ = ∑ S, ∑ T ∈ (univ : Finset (Fin n)).powersetCard k,
          μ S * (if T ⊆ S then F T else 0) := by
      apply Finset.sum_congr rfl
      intro S _
      rw [hsets S, Finset.sum_filter, Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro T _
      rw [prSup, Finset.sum_filter, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S _
      by_cases h : T ⊆ S <;> simp [h, mul_comm]

lemma cross_sum_le {ι κ : Type*} (Ts : Finset ι) (Rs : Finset κ)
    (a p x : ι → ℝ) (b q y : κ → ℝ) (α : ℝ)
    (ha : ∀ i ∈ Ts, 0 ≤ a i) (hb : ∀ j ∈ Rs, 0 ≤ b j)
    (h : ∀ i ∈ Ts, ∀ j ∈ Rs, p i * y j ≤ α * x i * q j) :
    (∑ i ∈ Ts, a i * p i) * (∑ j ∈ Rs, b j * y j) ≤
      α * (∑ i ∈ Ts, a i * x i) * (∑ j ∈ Rs, b j * q j) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  apply Finset.sum_le_sum
  intro i hi
  have h' := mul_le_mul_of_nonneg_left (h i hi j hj) (mul_nonneg (ha i hi) (hb j hj))
  nlinarith only [h']

lemma ratio_le_of_cross {N D Nx Dx α : ℝ} (hD : 0 < D) (hDx : 0 < Dx)
    (h : N * Dx ≤ α * Nx * D) : N / D ≤ α * (Nx / Dx) := by
  rw [← mul_div_assoc, div_le_div_iff₀ hD hDx]
  exact h


lemma exists_pos_weight_le {ι : Type*} [Fintype ι] (w f : ι → ℝ) (C : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i, w i)
    (havg : (∑ i, w i * f i) / (∑ i, w i) ≤ C) :
    ∃ i, 0 < w i ∧ f i ≤ C := by
  classical
  by_contra h
  push Not at h
  have hle : ∀ i, w i * C ≤ w i * f i := by
    intro i
    by_cases hi : w i = 0
    · simp [hi]
    · exact (mul_lt_mul_of_pos_left (h i (lt_of_le_of_ne (hw i) (Ne.symm hi)))
        (lt_of_le_of_ne (hw i) (Ne.symm hi))).le
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun i _ => hw i)).mp hW
  have hlt : (∑ i, w i * C) < ∑ i, w i * f i :=
    Finset.sum_lt_sum (fun i _ => hle i)
      ⟨i, Finset.mem_univ i, mul_lt_mul_of_pos_left (h i hi) hi⟩
  rw [← Finset.sum_mul] at hlt
  have hc := (div_le_iff₀ hW).mp havg
  nlinarith only [hlt, hc]

end PropVolSampling.Reduction.VOL7FiniteProof

end Inline_VOL_Finite

section Inline_VOL_ExpectationWeighted

namespace PropVolSampling.Reduction.VOL7WeightedProof
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

end PropVolSampling.Reduction.VOL7WeightedProof

end Inline_VOL_ExpectationWeighted


noncomputable section Inline_VOL7_Assembly
open Matrix Finset PropVolSampling.Reduction
open PropVolSampling.Reduction.VOL7FiniteProof PropVolSampling.Reduction.VOL7WeightedProof

namespace PropVolSampling.Reduction.VOL7Proof
lemma minor_nonneg {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (T : Finset (Fin n)) :
    0 ≤ ((colSub V T)ᵀ * colSub V T).det := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (colSub V T)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.det_nonneg
end PropVolSampling.Reduction.VOL7Proof

open PropVolSampling.Reduction.VOL7Proof

theorem solution {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (k : ℕ) (hd : 1 ≤ d) (hdk : d ≤ k)
    (hkn : k ≤ n) (x : Fin n → ℝ) (hx : IsRelaxFeasible k x) (hpd : (weightedGram V x).PosDef)
    (μ : Finset (Fin n) → ℝ) (hμ : IsSetDist k μ) (α : ℝ) (hα : IsApproxIndep d α x μ)
    (hZ : 0 < pvsNormalizer V μ) :
    pvsExpect V μ (fun S => aObj (gram V S)) ≤ α * aObj (weightedGram V x) := by
  classical
  clear hdk hkn
  obtain ⟨hnum, hden, he⟩ := expectation_ratio hd V k μ hμ hZ
  let m : Finset (Fin n) → ℝ := fun T => ((colSub V T)ᵀ * colSub V T).det
  let Ts := (univ : Finset (Fin n)).powersetCard (d-1)
  let Rs := (univ : Finset (Fin n)).powersetCard d
  have hDx : 0 < ∑ R ∈ Rs, m R * xPow x R := by
    change 0 < ∑ R ∈ (univ : Finset (Fin n)).powersetCard d,
      ((colSub V R)ᵀ * colSub V R).det * xPow x R
    rw [← weighted_det_eq_sum V x (fun i => (hx.1 i).1) hpd.isHermitian]
    exact hpd.det_pos
  have hD : 0 < ∑ R ∈ Rs, m R * prSup μ R := by
    change 0 < ∑ R ∈ (univ : Finset (Fin n)).powersetCard d,
      ((colSub V R)ᵀ * colSub V R).det * prSup μ R
    rw [← hden]
    exact hZ
  have hcross := cross_sum_le Ts Rs m (prSup μ) (xPow x) m (prSup μ) (xPow x) α
    (fun T _ => minor_nonneg V T) (fun R _ => minor_nonneg V R)
    (fun T hT R hR => hα T R (Finset.mem_powersetCard.mp hT).2
      (Finset.mem_powersetCard.mp hR).2)
  have hc := ratio_le_of_cross hD hDx hcross
  rw [hnum, hden] at he
  rw [relaxation_ratio hd V x (fun i => (hx.1 i).1) hpd]
  exact he.trans hc

end Inline_VOL7_Assembly
