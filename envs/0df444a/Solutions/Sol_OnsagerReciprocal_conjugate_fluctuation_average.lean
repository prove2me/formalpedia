-- Prove2me | solution 1 for OnsagerReciprocal.conjugate_fluctuation_average
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-10T23:37:40.618795+00:00
-- url     : https://prove2.me/submissions/b6217585-68fc-459b-9928-2e7f83404579

import Mathlib
import Definitions.Def_OnsagerReciprocal_basic
import Theorems.Thm_OnsagerReciprocal_integrable_norm_pow_mul_fluctuationWeight

open Matrix MeasureTheory
set_option autoImplicit false

private lemma abs_mulVec_le {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (i : Fin n) :
    |(β *ᵥ x) i| ≤ (∑ j, |β i j|) * ‖x‖ := by
  rw [Matrix.mulVec, dotProduct, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [abs_mul]
  have := norm_le_pi_norm x j
  rw [Real.norm_eq_abs] at this
  exact mul_le_mul_of_nonneg_left this (abs_nonneg _)

private lemma continuous_weight {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) :
    Continuous (OnsagerReciprocal.fluctuationWeight β) := by
  unfold OnsagerReciprocal.fluctuationWeight
  fun_prop

private lemma weight_pos {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    0 < OnsagerReciprocal.fluctuationWeight β x := Real.exp_pos _

private lemma quad_expand {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) (x v : Fin n → ℝ) (t : ℝ) :
    (x + t • v) ⬝ᵥ (β *ᵥ (x + t • v)) =
      x ⬝ᵥ (β *ᵥ x) + t * (v ⬝ᵥ (β *ᵥ x) + x ⬝ᵥ (β *ᵥ v)) + t ^ 2 * (v ⬝ᵥ (β *ᵥ v)) := by
  simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul]
  ring

private lemma hasLineDerivAt_weight {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) (hβ : βᵀ = β)
    (x : Fin n → ℝ) (i : Fin n) :
    HasLineDerivAt ℝ (OnsagerReciprocal.fluctuationWeight β)
      (-(β *ᵥ x) i * OnsagerReciprocal.fluctuationWeight β x) x (Pi.single i 1) := by
  unfold HasLineDerivAt OnsagerReciprocal.fluctuationWeight
  set v : Fin n → ℝ := Pi.single i 1
  have hq : HasDerivAt (fun t : ℝ => (x + t • v) ⬝ᵥ (β *ᵥ (x + t • v)))
      (v ⬝ᵥ (β *ᵥ x) + x ⬝ᵥ (β *ᵥ v)) 0 := by
    simp_rw [quad_expand]
    have h : HasDerivAt (fun t : ℝ => x ⬝ᵥ (β *ᵥ x) + t * (v ⬝ᵥ (β *ᵥ x) + x ⬝ᵥ (β *ᵥ v))
        + t ^ 2 * (v ⬝ᵥ (β *ᵥ v)))
        (1 * (v ⬝ᵥ (β *ᵥ x) + x ⬝ᵥ (β *ᵥ v)) + ((2:ℕ) * (0:ℝ) ^ (2 - 1)) * (v ⬝ᵥ (β *ᵥ v))) 0 :=
      (((hasDerivAt_id' (0:ℝ)).mul_const (v ⬝ᵥ (β *ᵥ x) + x ⬝ᵥ (β *ᵥ v))).const_add
        (x ⬝ᵥ (β *ᵥ x))).add ((hasDerivAt_pow 2 (0:ℝ)).mul_const (v ⬝ᵥ (β *ᵥ v)))
    exact h.congr_deriv (by simp)
  have h2 := (hq.const_mul (-(1 / 2 : ℝ))).exp
  have hsym : x ⬝ᵥ (β *ᵥ v) = (β *ᵥ x) i := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hβ, dotProduct_single, mul_one]
  have hv : v ⬝ᵥ (β *ᵥ x) = (β *ᵥ x) i := by
    rw [single_dotProduct, one_mul]
  refine h2.congr_deriv ?_
  simp only [zero_smul, add_zero, hsym, hv]
  ring

private lemma hasLineDerivAt_coord {n : ℕ} (x : Fin n → ℝ) (i k : Fin n) :
    HasLineDerivAt ℝ (fun y : Fin n → ℝ => y k) ((Pi.single i (1:ℝ) : Fin n → ℝ) k) x
      (Pi.single i 1) := by
  unfold HasLineDerivAt
  set v : Fin n → ℝ := Pi.single i 1
  have h : HasDerivAt (fun t : ℝ => x k + t * v k) (1 * v k) 0 :=
    ((hasDerivAt_id' (0:ℝ)).mul_const (v k)).const_add (x k)
  have h' : HasDerivAt (fun t : ℝ => (x + t • v) k) (1 * v k) 0 := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h
  exact h'.congr_deriv (one_mul _)

private lemma integrable_weight {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) (hβ : β.PosDef) :
    Integrable (OnsagerReciprocal.fluctuationWeight β) := by
  have := OnsagerReciprocal.integrable_norm_pow_mul_fluctuationWeight β hβ 0
  simpa only [pow_zero, one_mul] using this

private lemma integrable_coord_mul_weight {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ) (hβ : β.PosDef)
    (k : Fin n) :
    Integrable (fun x : Fin n → ℝ => x k * OnsagerReciprocal.fluctuationWeight β x) := by
  refine (OnsagerReciprocal.integrable_norm_pow_mul_fluctuationWeight β hβ 1).mono' ?_ ?_
  · have := continuous_weight β
    exact (by fun_prop : Continuous fun x : Fin n → ℝ =>
      x k * OnsagerReciprocal.fluctuationWeight β x).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, pow_one, Real.norm_of_nonneg (weight_pos β x).le]
    exact mul_le_mul_of_nonneg_right (norm_le_pi_norm x k) (weight_pos β x).le

private lemma integrable_coord_mul_conj_mul_weight {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (i k : Fin n) :
    Integrable (fun x : Fin n → ℝ =>
      x k * (-(β *ᵥ x) i * OnsagerReciprocal.fluctuationWeight β x)) := by
  refine ((OnsagerReciprocal.integrable_norm_pow_mul_fluctuationWeight β hβ 2).const_mul
    (∑ j, |β i j|)).mono' ?_ ?_
  · have := continuous_weight β
    have hc : Continuous fun x : Fin n → ℝ => (β *ᵥ x) i := by fun_prop
    exact (by fun_prop : Continuous fun x : Fin n → ℝ =>
      x k * (-(β *ᵥ x) i * OnsagerReciprocal.fluctuationWeight β x)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    have hw := (weight_pos β x).le
    have h1 := norm_le_pi_norm x k
    have h2 := abs_mulVec_le β x i
    rw [norm_mul, norm_mul, norm_neg, Real.norm_of_nonneg hw, Real.norm_eq_abs ((β *ᵥ x) i)]
    have hC : 0 ≤ ∑ j, |β i j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    calc ‖x k‖ * (|(β *ᵥ x) i| * OnsagerReciprocal.fluctuationWeight β x)
        ≤ ‖x‖ * (((∑ j, |β i j|) * ‖x‖) * OnsagerReciprocal.fluctuationWeight β x) := by
          gcongr
      _ = (∑ j, |β i j|) * (‖x‖ ^ 2 * OnsagerReciprocal.fluctuationWeight β x) := by ring

theorem solution {n : ℕ} (β : Matrix (Fin n) (Fin n) ℝ)
    (hβ : β.PosDef) (i k : Fin n) :
    OnsagerReciprocal.fluctuationAverage β (fun x => OnsagerReciprocal.conjugate β x i * x k) =
      if i = k then 1 else 0 := by
  have hsymm : βᵀ = β := by
    have h := hβ.1
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at h
    exact h
  set w := OnsagerReciprocal.fluctuationWeight β with hw_def
  set v : Fin n → ℝ := Pi.single i 1 with hv_def
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Fin n → ℝ))) (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := fun x : Fin n → ℝ => x k) (f' := fun _ => v k) (g := w)
    (g' := fun x => -(β *ᵥ x) i * w x) (v := v)
    (by simpa only [ContinuousLinearMap.mul_apply'] using
      (integrable_weight β hβ).const_mul (v k))
    (by simpa only [ContinuousLinearMap.mul_apply'] using
      integrable_coord_mul_conj_mul_weight β hβ i k)
    (by simpa only [ContinuousLinearMap.mul_apply'] using
      integrable_coord_mul_weight β hβ k)
    (fun x _ => hasLineDerivAt_coord x i k)
    (fun x _ => hasLineDerivAt_weight β hsymm x i)
  simp only [ContinuousLinearMap.mul_apply'] at hibp
  have hZ : 0 < ∫ x, w x := by
    have := integrable_weight β hβ
    exact integral_exp_pos this
  have key : ∫ x, (β *ᵥ x) i * x k * w x = v k * ∫ x, w x := by
    rw [integral_const_mul] at hibp
    have : (fun x : Fin n → ℝ => x k * (-(β *ᵥ x) i * w x)) =
        fun x => -((β *ᵥ x) i * x k * w x) := by
      funext x; ring
    rw [this, integral_neg] at hibp
    linarith
  unfold OnsagerReciprocal.fluctuationAverage OnsagerReciprocal.conjugate
  rw [key, mul_div_assoc, div_self hZ.ne', mul_one, hv_def, Pi.single_apply]
  by_cases h : i = k
  · subst h; simp
  · simp [h, Ne.symm h]
