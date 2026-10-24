-- Prove2me | solution 1 for PropVolSampling.Reduction.theorem_1_3
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T09:15:33.783039+00:00
-- url     : https://prove2.me/submissions/5ee5fed8-b798-47c2-9741-20d5f8015873

import Mathlib
import Definitions.Def_PropVolSampling_Reduction_Model
import Theorems.Thm_PropVolSampling_Reduction_inequality_5
import Theorems.Thm_PropVolSampling_Reduction_padding
import Theorems.Thm_PropVolSampling_Reduction_cp_le_opt


noncomputable section Inline_VOL_Finite
open Matrix Finset
namespace PropVolSampling.Reduction.VOLMFiniteProof

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

end PropVolSampling.Reduction.VOLMFiniteProof

end Inline_VOL_Finite


noncomputable section Inline_VOL_Support

open Matrix Finset

namespace PropVolSampling.Reduction.VOLMSupportProof

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

end PropVolSampling.Reduction.VOLMSupportProof

end Inline_VOL_Support


noncomputable section Inline_VOLM_Assembly
open Matrix Finset
namespace PropVolSampling.Reduction.VOLMProof
open VOLMSupportProof VOLMFiniteProof

/-- The frozen padding branch's direct Gram inclusion argument. -/
lemma gram_posDef_of_subset {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (S S' : Finset (Fin n)) (hSS' : S ⊆ S') (hpd : (gram V S).PosDef) :
    (gram V S').PosDef := by
  have hsub : gram V S' - gram V S = gram V (S' \ S) := by
    simp only [gram_eq_sum]
    exact (Finset.sum_sdiff_eq_sub (f := fun i =>
      vecMulVec (fun a => V a i) (fun a => V a i)) hSS').symm
  have hpsd : (gram V S' - gram V S).PosSemidef := by
    rw [hsub]
    exact gram_posSemidef V (S' \ S)
  simpa only [add_sub_cancel] using hpd.add_posSemidef hpsd

lemma padded_expect_le {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (μ : Finset (Fin n) → ℝ) (hμ : ∀ S, 0 ≤ μ S) (hZ : 0 < pvsNormalizer V μ)
    (pad : Finset (Fin n) → Finset (Fin n)) (hpad : ∀ S, μ S ≠ 0 → S ⊆ pad S) :
    pvsExpect V μ (fun S => aObj (gram V (pad S))) ≤
      pvsExpect V μ (fun S => aObj (gram V S)) := by
  unfold pvsExpect
  apply Finset.sum_le_sum
  intro S _
  by_cases hw : pvsWeight V μ S = 0
  · simp [hw]
  have hwp := lt_of_le_of_ne (pvsWeight_nonneg V μ hμ S) (Ne.symm hw)
  obtain ⟨hμS, hpd⟩ := pvsWeight_pos_support_ne_zero V μ S hwp
  exact mul_le_mul_of_nonneg_left (padding V S (pad S) (hpad S hμS) hpd)
    (div_nonneg hwp.le hZ.le)

lemma pvsExpect_eq_ratio {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ)
    (μ : Finset (Fin n) → ℝ) (f : Finset (Fin n) → ℝ) :
    pvsExpect V μ f = (∑ S, pvsWeight V μ S * f S) / (∑ S, pvsWeight V μ S) := by
  simp only [pvsExpect, pvsNormalizer, div_mul_eq_mul_div, Finset.sum_div]

end PropVolSampling.Reduction.VOLMProof

open PropVolSampling.Reduction PropVolSampling.Reduction.VOLMProof
open PropVolSampling.Reduction.VOLMSupportProof PropVolSampling.Reduction.VOLMFiniteProof

theorem solution {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℝ) (k : ℕ) (hd : 1 ≤ d) (hdk : d ≤ k)
    (hkn : k ≤ n) (x : Fin n → ℝ) (hx : IsRelaxOptimal V k x)
    (μ : Finset (Fin n) → ℝ) (hμ : IsSetDist k μ) (α : ℝ) (hα : IsApproxIndep d α x μ)
    (hZ : 0 < pvsNormalizer V μ) (pad : Finset (Fin n) → Finset (Fin n))
    (hpad : ∀ S, μ S ≠ 0 → S ⊆ pad S ∧ (pad S).card = k) :
    (∀ Sopt : Finset (Fin n), Sopt.card = k → (gram V Sopt).PosDef →
      pvsExpect V μ (fun S => aObj (gram V (pad S))) ≤ α * aObj (gram V Sopt)) ∧
    ∃ S : Finset (Fin n), S.card = k ∧ (gram V S).PosDef ∧
      aObj (gram V S) ≤ α * aObj (weightedGram V x) := by
  have he := inequality_5 V k hd hdk hkn x hx.1 hx.2.1 μ hμ α hα hZ
  have hp := padded_expect_le V μ hμ.1 hZ pad (fun S hS => (hpad S hS).1)
  have hCP := aObj_pos_of_posDef hd (weightedGram V x) hx.2.1
  have hE0 := pvsExpect_nonneg V μ hμ.1 (fun S => aObj (gram V S)) (gram_aObj_nonneg V)
  have hα0 : 0 ≤ α := by nlinarith only [he, hCP, hE0]
  refine ⟨?_, ?_⟩
  · intro S hS hpd
    exact (hp.trans he).trans (mul_le_mul_of_nonneg_left (cp_le_opt V k x hx S hS hpd) hα0)
  · have havg := hp.trans he
    rw [pvsExpect_eq_ratio] at havg
    obtain ⟨S, hS, hval⟩ := exists_pos_weight_le (pvsWeight V μ)
      (fun S => aObj (gram V (pad S))) (α * aObj (weightedGram V x))
      (pvsWeight_nonneg V μ hμ.1) hZ havg
    obtain ⟨hμS, hpd⟩ := pvsWeight_pos_support_ne_zero V μ S hS
    exact ⟨pad S, (hpad S hμS).2,
      gram_posDef_of_subset V S (pad S) (hpad S hμS).1 hpd, hval⟩

end Inline_VOLM_Assembly
