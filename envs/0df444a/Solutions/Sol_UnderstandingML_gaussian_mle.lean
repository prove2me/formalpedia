-- Prove2me | solution 1 for UnderstandingML.gaussian_mle
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-26T15:34:34.928777+00:00
-- url     : https://prove2.me/submissions/59a7bd62-6398-4e78-bdbd-ae4d9c0f0b47

import Definitions.Def_UnderstandingML_Generative

open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

open UnderstandingML

/-- Steiner decomposition: `∑ (xᵢ − μ)² = ∑ (xᵢ − μ̂)² + m (μ̂ − μ)²`. -/
private lemma gaussian_sum_sq_decomp {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) (μ : ℝ) :
    ∑ i, (x i - μ) ^ 2 = ∑ i, (x i - sampleMean x) ^ 2 + m * (sampleMean x - μ) ^ 2 := by
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hsum : ∑ i, x i = m * sampleMean x := by
    unfold sampleMean; field_simp
  have e : ∀ i, (x i - μ) ^ 2 = (x i - sampleMean x) ^ 2 +
      2 * (sampleMean x - μ) * x i + ((sampleMean x - μ) ^ 2 - 2 * (sampleMean x - μ) * sampleMean x) := by
    intro i; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, hsum]
  ring

theorem solution {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) (hσ : 0 < sampleStd x) (μ σ : ℝ)
    (hσpos : 0 < σ) :
    gaussianLogLik x μ σ ≤ gaussianLogLik x (sampleMean x) (sampleStd x) := by
  set s := sampleStd x with hs_def
  set A := ∑ i, (x i - sampleMean x) ^ 2 with hA
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hs2 : s ^ 2 = A / m := by
    rw [hs_def, sampleStd, Real.sq_sqrt (div_nonneg hA0 hmR.le)]
  have hB : A ≤ ∑ i, (x i - μ) ^ 2 := by
    rw [gaussian_sum_sq_decomp hm x μ]; nlinarith [sq_nonneg (sampleMean x - μ)]
  have hc : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  unfold gaussianLogLik
  rw [Real.log_mul hσpos.ne' hc.ne', Real.log_mul hσ.ne' hc.ne']
  -- reduce to `A/(2σ²) + m log σ ≥ m/2 + m log s`
  have hA' : A = m * s ^ 2 := by rw [hs2]; field_simp
  have key : Real.log (s ^ 2 / σ ^ 2) ≤ s ^ 2 / σ ^ 2 - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_pow] at key
  have h1 : -(1 / (2 * σ ^ 2)) * ∑ i, (x i - μ) ^ 2 ≤ -(1 / (2 * σ ^ 2)) * A := by
    have : 0 ≤ 1 / (2 * σ ^ 2) := by positivity
    nlinarith
  have h2 : -(1 / (2 * s ^ 2)) * ∑ i, (x i - sampleMean x) ^ 2 = -(m : ℝ) / 2 := by
    rw [← hA, hA']; field_simp
  have h3 : -(1 / (2 * σ ^ 2)) * A = -(m : ℝ) / 2 * (s ^ 2 / σ ^ 2) := by
    rw [hA']; field_simp
  rw [h2]
  push_cast at key
  nlinarith [mul_le_mul_of_nonneg_left key hmR.le]
