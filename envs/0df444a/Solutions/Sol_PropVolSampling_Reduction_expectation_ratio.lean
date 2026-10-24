-- Prove2me | solution 1 for PropVolSampling.Reduction.expectation_ratio
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:05:54.189143+00:00
-- url     : https://prove2.me/submissions/48a59d70-b246-47ad-b80e-afe6c70d2042

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model
import Theorems.Thm_PropVolSampling_Reduction_lemma_2_1
import Theorems.Thm_PropVolSampling_Reduction_identity_4
import Theorems.Thm_PropVolSampling_Reduction_identity_6


noncomputable section Inline_VOL_Finite
open Matrix Finset
namespace PropVolSampling.Reduction.VOL6FiniteProof

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

end PropVolSampling.Reduction.VOL6FiniteProof

end Inline_VOL_Finite


noncomputable section Inline_VOL_Support

open Matrix Finset

namespace PropVolSampling.Reduction.VOL6SupportProof

/-- Reused verbatim from the frozen direct VOL3 Gram argument. -/
lemma gram_posSemidef {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) : (gram V S).PosSemidef := by
  simpa only [gram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_self_mul_conjTranspose (colSub V S)

lemma gram_det_nonneg {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) : 0 ≤ (gram V S).det :=
  (gram_posSemidef V S).det_nonneg

lemma gram_eq_sum {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) :
    gram V S = ∑ i ∈ S, vecMulVec (fun a => V a i) (fun a => V a i) := by
  ext a b
  simp [gram, colSub, Matrix.mul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply]
  exact Finset.sum_attach S (fun i => V a i * V b i)

lemma weightedGram_indicator {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) :
    weightedGram V (fun i => if i ∈ S then 1 else 0) = gram V S := by
  rw [gram_eq_sum]
  simp [weightedGram, ite_smul]


lemma weightedGram_posSemidef {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) : (weightedGram V x).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  apply Matrix.PosSemidef.smul _ (hx i)
  simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (fun a => V a i)

lemma aObj_nonneg_of_posSemidef {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.PosSemidef) : 0 ≤ aObj M :=
  hM.inv.trace_nonneg

lemma gram_aObj_nonneg {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) : 0 ≤ aObj (gram V S) :=
  aObj_nonneg_of_posSemidef _ (gram_posSemidef V S)

lemma aObj_pos_of_posDef {d : ℕ} (hd : 1 ≤ d) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.PosDef) : 0 < aObj M := by
  let : NeZero d := ⟨by omega⟩
  exact hM.inv.trace_pos

lemma aObj_eq_zero_of_det_eq_zero {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : M.det = 0) : aObj M = 0 := by
  simp [aObj, Matrix.nonsing_inv_apply_not_isUnit M (by simp [hM])]

lemma gram_posDef_of_det_ne_zero {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) (hdet : (gram V S).det ≠ 0) : (gram V S).PosDef :=
  (gram_posSemidef V S).posDef_iff_det_ne_zero.mpr hdet

lemma gram_posDef_of_det_pos {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) (hdet : 0 < (gram V S).det) : (gram V S).PosDef :=
  gram_posDef_of_det_ne_zero V S hdet.ne'

lemma pvsWeight_nonneg {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (μ : Finset (Fin n) → ℝ) (hμ : ∀ S, 0 ≤ μ S) (S : Finset (Fin n)) :
    0 ≤ pvsWeight V μ S :=
  mul_nonneg (hμ S) (gram_det_nonneg V S)

/-- Strict sampling weight implies positive μ and positive definite Gram;
    positivity of μ alone is deliberately insufficient. -/
lemma pvsWeight_pos_support {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (μ : Finset (Fin n) → ℝ) (S : Finset (Fin n)) (hS : 0 < pvsWeight V μ S) :
    0 < μ S ∧ (gram V S).PosDef := by
  change 0 < μ S * (gram V S).det at hS
  rcases mul_pos_iff.mp hS with h | h
  · exact ⟨h.1, gram_posDef_of_det_pos V S h.2⟩
  · exact False.elim (not_lt_of_ge (gram_det_nonneg V S) h.2)

lemma pvsWeight_pos_support_ne_zero {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (μ : Finset (Fin n) → ℝ) (S : Finset (Fin n)) (hS : 0 < pvsWeight V μ S) :
    μ S ≠ 0 ∧ (gram V S).PosDef :=
  ⟨(pvsWeight_pos_support V μ S hS).1.ne', (pvsWeight_pos_support V μ S hS).2⟩

lemma pvsNormalizer_nonneg {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (μ : Finset (Fin n) → ℝ) (hμ : ∀ S, 0 ≤ μ S) : 0 ≤ pvsNormalizer V μ :=
  Finset.sum_nonneg fun S _ => pvsWeight_nonneg V μ hμ S

lemma pvsExpect_nonneg {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (μ : Finset (Fin n) → ℝ) (hμ : ∀ S, 0 ≤ μ S)
    (f : Finset (Fin n) → ℝ) (hf : ∀ S, 0 ≤ f S) : 0 ≤ pvsExpect V μ f :=
  Finset.sum_nonneg fun S _ => mul_nonneg
    (div_nonneg (pvsWeight_nonneg V μ hμ S) (pvsNormalizer_nonneg V μ hμ)) (hf S)

end PropVolSampling.Reduction.VOL6SupportProof

end Inline_VOL_Support

section Inline_VOL_ExpectationWeighted

namespace PropVolSampling.Reduction.VOL6WeightedProof
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

end PropVolSampling.Reduction.VOL6WeightedProof

end Inline_VOL_ExpectationWeighted


noncomputable section Inline_VOL6_Assembly
open Matrix Finset
namespace PropVolSampling.Reduction.VOL6Proof
open VOL6FiniteProof VOL6SupportProof VOL6WeightedProof

lemma minor_nonneg {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (T : Finset (Fin n)) :
    0 ≤ ((colSub V T)ᵀ * colSub V T).det := by
  have h := Matrix.posSemidef_conjTranspose_mul_self (colSub V T)
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.det_nonneg

lemma gram_Ek {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) (k : ℕ) (hk : k ≤ d) :
    Ek k (gram V S) = ∑ T ∈ S.powersetCard k, ((colSub V T)ᵀ * colSub V T).det := by
  classical
  rw [← weightedGram_indicator V S, weighted_Ek V _
    (by intro i; split_ifs <;> norm_num) k hk]
  simp_rw [xPow_indicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  tauto

lemma gram_Ek_nonneg {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) (k : ℕ) (hk : k ≤ d) : 0 ≤ Ek k (gram V S) := by
  rw [gram_Ek V S k hk]
  exact Finset.sum_nonneg fun T _ => minor_nonneg V T

lemma gram_det_expansion {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S : Finset (Fin n)) :
    (gram V S).det = ∑ T ∈ S.powersetCard d, ((colSub V T)ᵀ * colSub V T).det := by
  have he : Ek d (gram V S) = (gram V S).det := by
    simpa only [Fintype.card_fin] using Ek_card_eq_det (gram V S) (gram_posSemidef V S).isHermitian
  rw [← he, gram_Ek V S d le_rfl]

lemma weighted_aObj_le_Ek {d n : ℕ} (hd : 1 ≤ d) (V : Matrix (Fin d) (Fin n) ℝ)
    (μ : Finset (Fin n) → ℝ) (hμ : ∀ S, 0 ≤ μ S) (S : Finset (Fin n)) :
    μ S * (gram V S).det * aObj (gram V S) ≤ μ S * Ek (d-1) (gram V S) := by
  by_cases hdet : (gram V S).det = 0
  · simp only [hdet, mul_zero, zero_mul]
    exact mul_nonneg (hμ S) (gram_Ek_nonneg V S (d-1) (Nat.sub_le _ _))
  · rw [identity_6 hd _ (gram_posSemidef V S).isHermitian hdet]
    exact le_of_eq (by field_simp)

lemma expectation_le_ratio {d n : ℕ} (hd : 1 ≤ d) (V : Matrix (Fin d) (Fin n) ℝ)
    (μ : Finset (Fin n) → ℝ) (hμ : ∀ S, 0 ≤ μ S) (hZ : 0 < pvsNormalizer V μ) :
    pvsExpect V μ (fun S => aObj (gram V S)) ≤
      (∑ S, μ S * Ek (d-1) (gram V S)) / pvsNormalizer V μ := by
  unfold pvsExpect pvsWeight
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun S _ => weighted_aObj_le_Ek hd V μ hμ S) hZ.le

end PropVolSampling.Reduction.VOL6Proof

open PropVolSampling.Reduction PropVolSampling.Reduction.VOL6Proof
open PropVolSampling.Reduction.VOL6FiniteProof

theorem solution {d n : ℕ} (hd : 1 ≤ d) (V : Matrix (Fin d) (Fin n) ℝ) (k : ℕ)
    (μ : Finset (Fin n) → ℝ) (hμ : IsSetDist k μ) (hZ : 0 < pvsNormalizer V μ) :
    (∑ S, μ S * Ek (d - 1) (gram V S) =
        ∑ T ∈ powersetCard (d - 1) (univ : Finset (Fin n)),
          ((colSub V T)ᵀ * colSub V T).det * prSup μ T) ∧
      (pvsNormalizer V μ =
        ∑ R ∈ powersetCard d (univ : Finset (Fin n)),
          ((colSub V R)ᵀ * colSub V R).det * prSup μ R) ∧
      pvsExpect V μ (fun S => aObj (gram V S)) ≤
        (∑ S, μ S * Ek (d - 1) (gram V S)) / pvsNormalizer V μ := by
  refine ⟨?_, ?_, expectation_le_ratio hd V μ hμ.1 hZ⟩
  · simp_rw [gram_Ek V _ (d-1) (Nat.sub_le _ _)]
    exact sum_subset_swap _ _ _
  · unfold pvsNormalizer pvsWeight
    simp_rw [gram_det_expansion]
    exact sum_subset_swap _ _ _

end Inline_VOL6_Assembly
