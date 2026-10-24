-- Prove2me | solution 1 for PigeonholeDesign.MultiDim.lemma_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T04:14:12.403631+00:00
-- url     : https://prove2.me/submissions/b4a3455b-c907-4c11-83e4-19ce723df46a

import Mathlib

open MeasureTheory ProbabilityTheory Real

namespace EC1Aux

lemma hoeff_scalar (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (t : ℝ) :
    α * exp (t * (1 - α)) + (1 - α) * exp (t * (-α)) ≤ exp (t ^ 2 / 8) := by
  set μ : Measure ℝ := ENNReal.ofReal α • Measure.dirac (1 - α) +
    ENNReal.ofReal (1 - α) • Measure.dirac (-α) with hμ
  have h1' : 0 ≤ 1 - α := by linarith
  have hprob : IsProbabilityMeasure μ := by
    constructor
    simp only [hμ, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
      measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add h0 h1']
    simp
  have hint : ∀ f : ℝ → ℝ, ∫ x, f x ∂μ = α * f (1 - α) + (1 - α) * f (-α) := by
    intro f
    rw [hμ, integral_add_measure, integral_smul_measure, integral_smul_measure, integral_dirac,
      integral_dirac]
    · simp [ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal h1']
    · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
    · exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top
  have hmean : μ[id] = 0 := by
    rw [hint]; simp; ring
  have hb : ∀ᵐ ω ∂μ, id ω ∈ Set.Icc (-α) (1 - α) := by
    rw [hμ, ae_add_measure_iff]
    constructor
    · refine Measure.ae_smul_measure ?_ _
      rw [ae_dirac_eq, Filter.eventually_pure]
      simp only [id, Set.mem_Icc]; constructor <;> linarith
    · refine Measure.ae_smul_measure ?_ _
      rw [ae_dirac_eq, Filter.eventually_pure]
      simp only [id, Set.mem_Icc]; constructor <;> linarith
  have hsub := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (X := id) (μ := μ)
    aemeasurable_id hb hmean
  have hle := hsub.mgf_le t
  rw [mgf, hint] at hle
  simp only [id] at hle
  have hc : ((‖(1 - α) - -α‖₊ / 2) ^ 2 : NNReal) = 1 / 4 := by
    rw [show (1 - α) - (-α) = (1 : ℝ) by ring]; simp; norm_num
  refine hle.trans (le_of_eq ?_)
  rw [hc]; push_cast; ring_nf


lemma mgf_binom (n : ℕ) (α t : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * α ^ k * (1 - α) ^ (n - k) *
        exp (t * (k - α * n)) =
      (α * exp (t * (1 - α)) + (1 - α) * exp (t * (-α))) ^ n := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simp at hk; omega
  rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  have : (k : ℝ) * (t * (1 - α)) + ((n - k : ℕ) : ℝ) * (t * (-α)) = t * (k - α * n) := by
    rw [Nat.cast_sub hk']; ring
  rw [← this, Real.exp_add]; ring

lemma tail (n : ℕ) (α : ℝ) (h0 : 0 ≤ α) (h1 : α ≤ 1) (t u : ℝ) :
    ∑ k ∈ Finset.range (n + 1), (if u ≤ t * (k - α * n) then
        (n.choose k : ℝ) * α ^ k * (1 - α) ^ (n - k) else 0) ≤
      exp (-u) * exp (t ^ 2 / 8) ^ n := by
  have h1' : 0 ≤ 1 - α := by linarith
  calc ∑ k ∈ Finset.range (n + 1), (if u ≤ t * (k - α * n) then
        (n.choose k : ℝ) * α ^ k * (1 - α) ^ (n - k) else 0)
      ≤ ∑ k ∈ Finset.range (n + 1), exp (-u) * ((n.choose k : ℝ) * α ^ k * (1 - α) ^ (n - k) *
          exp (t * (k - α * n))) := by
        apply Finset.sum_le_sum
        intro k _
        have hw : 0 ≤ (n.choose k : ℝ) * α ^ k * (1 - α) ^ (n - k) := by positivity
        split_ifs with h
        · have : 1 ≤ exp (-u) * exp (t * (k - α * n)) := by
            rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
          nlinarith
        · positivity
    _ = exp (-u) * (α * exp (t * (1 - α)) + (1 - α) * exp (t * (-α))) ^ n := by
        rw [← Finset.mul_sum, mgf_binom]
    _ ≤ exp (-u) * exp (t ^ 2 / 8) ^ n := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        exact pow_le_pow_left₀ (by positivity) (hoeff_scalar α h0 h1 t) n

end EC1Aux

open EC1Aux in
theorem solution (n : ℕ) (hn : 1 ≤ n) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    1 - 2 / (n : ℝ) ^ 2 ≤
      ∑ k ∈ (Finset.range (n + 1)).filter
          (fun k : ℕ => |(k : ℝ) - α * n| ≤ Real.sqrt (n * Real.log n)),
        (n.choose k : ℝ) * α ^ k * (1 - α) ^ (n - k) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set L := Real.log n with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast hn)
  set s := Real.sqrt (n * L) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = n * L := Real.sq_sqrt (by positivity)
  set w : ℕ → ℝ := fun k => (n.choose k : ℝ) * α ^ k * (1 - α) ^ (n - k) with hw
  have htot : ∑ k ∈ Finset.range (n + 1), w k = 1 := by
    have := (add_pow α (1 - α) n).symm
    rw [show α + (1 - α) = 1 by ring, one_pow] at this
    rw [← this]
    apply Finset.sum_congr rfl; intro k _; simp only [hw]; ring
  set t := 4 * s / n with ht
  have ht0 : 0 ≤ t := by positivity
  have hbound : exp (-(t * s)) * exp (t ^ 2 / 8) ^ n = 1 / (n : ℝ) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    have : -(t * s) + n * (t ^ 2 / 8) = -(L + L) := by
      rw [ht]; field_simp; rw [hs2]; ring
    rw [this, Real.exp_neg, Real.exp_add, Real.exp_log hnpos]
    field_simp
  have hbound' : exp (-(t * s)) * exp ((-t) ^ 2 / 8) ^ n = 1 / (n : ℝ) ^ 2 := by
    rw [neg_sq]; exact hbound
  have hup := tail n α hα0 hα1 t (t * s)
  have hlo := tail n α hα0 hα1 (-t) (t * s)
  rw [hbound] at hup
  rw [hbound'] at hlo
  rw [Finset.sum_filter]
  have key : ∀ k ∈ Finset.range (n + 1), w k ≤
      (if |(k : ℝ) - α * n| ≤ s then w k else 0) +
      ((if t * s ≤ t * (k - α * n) then w k else 0) +
       (if t * s ≤ -t * (k - α * n) then w k else 0)) := by
    intro k _
    have h1α : 0 ≤ 1 - α := by linarith
    have hwk : 0 ≤ w k := by simp only [hw]; positivity
    by_cases hP : |(k : ℝ) - α * n| ≤ s
    · rw [if_pos hP]
      have h1 : 0 ≤ (if t * s ≤ t * (k - α * n) then w k else 0) := by split_ifs <;> linarith
      have h2 : 0 ≤ (if t * s ≤ -t * (k - α * n) then w k else 0) := by split_ifs <;> linarith
      linarith
    · rw [if_neg hP]
      push Not at hP
      rcases lt_abs.1 hP with h | h
      · have : t * s ≤ t * (k - α * n) := mul_le_mul_of_nonneg_left h.le ht0
        rw [if_pos this]
        have h2 : 0 ≤ (if t * s ≤ -t * (k - α * n) then w k else 0) := by split_ifs <;> linarith
        linarith
      · have : t * s ≤ -t * (k - α * n) := by
          rw [neg_mul, ← mul_neg]; exact mul_le_mul_of_nonneg_left h.le ht0
        rw [if_pos this]
        have h1 : 0 ≤ (if t * s ≤ t * (k - α * n) then w k else 0) := by split_ifs <;> linarith
        linarith
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, htot] at hsum
  have e1 : ∑ k ∈ Finset.range (n + 1), (if t * s ≤ t * (k - α * n) then w k else 0) ≤
      1 / (n : ℝ) ^ 2 := hup
  have e2 : ∑ k ∈ Finset.range (n + 1), (if t * s ≤ -t * (k - α * n) then w k else 0) ≤
      1 / (n : ℝ) ^ 2 := hlo
  have : 2 / (n : ℝ) ^ 2 = 1 / (n : ℝ) ^ 2 + 1 / (n : ℝ) ^ 2 := by ring
  linarith
