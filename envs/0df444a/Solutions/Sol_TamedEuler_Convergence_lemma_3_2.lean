-- Prove2me | solution 1 for TamedEuler.Convergence.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:37:45.98529+00:00
-- url     : https://prove2.me/submissions/cc5e9083-7b95-470f-ad24-2cc01fdf36e3

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace L32

lemma pdf_mul_exp (a : ℝ) (x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (a * x ^ 2)
      = (√(2 * Real.pi))⁻¹ * Real.exp (-((1 - 2 * a) / 2) * x ^ 2) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma one_dim (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) :
    Integrable (fun x : ℝ => Real.exp (a * x ^ 2)) (gaussianReal 0 1) ∧
    ∫ x : ℝ, Real.exp (a * x ^ 2) ∂(gaussianReal 0 1) = (1 - 2 * a) ^ (-(1 : ℝ) / 2) := by
  have hb : 0 < (1 - 2 * a) / 2 := by linarith
  have hint : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * Real.exp (a * x ^ 2)) := by
    simp_rw [pdf_mul_exp]
    exact (integrable_exp_neg_mul_sq hb).const_mul _
  refine ⟨?_, ?_⟩
  · rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF _ _)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    simpa [toReal_gaussianPDF, smul_eq_mul] using hint
  · rw [integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp_rw [smul_eq_mul, pdf_mul_exp]
    rw [integral_const_mul, integral_gaussian]
    have h2 : (0:ℝ) < 1 - 2 * a := by linarith
    have e1 : Real.pi / ((1 - 2 * a) / 2) = 2 * Real.pi * (1 - 2 * a)⁻¹ := by
      field_simp
    have hpi : 0 < 2 * Real.pi := by positivity
    rw [e1, Real.sqrt_mul hpi.le, Real.sqrt_inv]
    have e2 : (1 - 2 * a) ^ (-(1 : ℝ) / 2) = (√(1 - 2 * a))⁻¹ := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h2.le]
      congr 1
      ring
    rw [e2]
    have : 0 < √(2 * Real.pi) := Real.sqrt_pos.2 hpi
    field_simp

lemma pow_eq (a : ℝ) (h2 : 0 < 1 - 2 * a) (n : ℕ) :
    ((1 - 2 * a) ^ (-(1 : ℝ) / 2)) ^ n = (1 - 2 * a) ^ (-(n : ℝ) / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul h2.le]
  congr 1
  ring

lemma ineq (a : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ 1 / 4) (n : ℕ) :
    (1 - 2 * a) ^ (-(n : ℝ) / 2) ≤ Real.exp (2 * a * n) := by
  have h2 : 0 < 1 - 2 * a := by linarith
  have hexp : Real.exp (-(4 * a)) ≤ 1 - 2 * a := by
    set t := 4 * a with ht
    have ht0 : 0 ≤ t := by linarith
    have ht1 : t ≤ 1 := by linarith
    have hq := Real.quadratic_le_exp_of_nonneg ht0
    have hpos : 0 < Real.exp t := Real.exp_pos t
    rw [Real.exp_neg]
    have h3 : 0 < 1 + t + t ^ 2 / 2 := by positivity
    have h4 : 1 ≤ (1 - t / 2) * (1 + t + t ^ 2 / 2) := by
      nlinarith [mul_nonneg ht0 (sub_nonneg.2 ht1), mul_nonneg ht0 ht0, mul_nonneg (mul_nonneg ht0 ht0) (sub_nonneg.2 ht1)]
    have h5 : 1 ≤ (1 - t / 2) * Real.exp t := by
      calc (1:ℝ) ≤ (1 - t / 2) * (1 + t + t ^ 2 / 2) := h4
        _ ≤ (1 - t / 2) * Real.exp t := by
          apply mul_le_mul_of_nonneg_left hq; linarith
    have : 1 - 2 * a = 1 - t / 2 := by rw [ht]; ring
    rw [this, inv_le_iff_one_le_mul₀ hpos]
    linarith
  have hn : -(n : ℝ) / 2 ≤ 0 := by
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  calc (1 - 2 * a) ^ (-(n : ℝ) / 2) ≤ (Real.exp (-(4 * a))) ^ (-(n : ℝ) / 2) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) hexp hn
    _ = Real.exp (2 * a * n) := by
        rw [← Real.exp_mul]
        congr 1
        ring

end L32

open L32 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (n : ℕ) (hn : 1 ≤ n) (Z : Ω → EuclideanSpace ℝ (Fin n))
    (hZ : HasLaw Z (stdGaussian (EuclideanSpace ℝ (Fin n))) P) :
    ∀ a : ℝ, a ∈ Set.Icc (0 : ℝ) (1 / 4) →
      ∫⁻ ω, ENNReal.ofReal (Real.exp (a * ‖Z ω‖ ^ 2)) ∂P
          = ENNReal.ofReal ((1 - 2 * a) ^ (-(n : ℝ) / 2)) ∧
        (1 - 2 * a) ^ (-(n : ℝ) / 2) ≤ Real.exp (2 * a * n) := by
  intro a ha
  obtain ⟨ha0, ha1⟩ := ha
  refine ⟨?_, ineq a ha0 ha1 n⟩
  have h2 : 0 < 1 - 2 * a := by linarith
  have hf : Measurable (fun z : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal (Real.exp (a * ‖z‖ ^ 2))) := by fun_prop
  rw [hZ.lintegral_comp hf.aemeasurable, ← map_pi_eq_stdGaussian,
    lintegral_map hf (by fun_prop)]
  have key : ∀ x : Fin n → ℝ,
      ENNReal.ofReal (Real.exp (a * ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2))
        = ENNReal.ofReal (∏ i, Real.exp (a * x i ^ 2)) := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Real.exp_sum]
  simp_rw [key]
  obtain ⟨hI, hV⟩ := one_dim a ha0 ha1
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (f := fun (_ : Fin n) (y : ℝ) => Real.exp (a * y ^ 2))
      (μ := fun _ => gaussianReal 0 1) (fun _ => hI))
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le)]
  rw [integral_fintype_prod_eq_pow (fun y : ℝ => Real.exp (a * y ^ 2)), hV]
  simp [pow_eq a h2 n]
