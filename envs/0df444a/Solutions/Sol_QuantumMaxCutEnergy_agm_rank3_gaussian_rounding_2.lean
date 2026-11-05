-- Prove2me | solution 2 for QuantumMaxCutEnergy.agm_rank3_gaussian_rounding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T23:04:07.207384+00:00
-- url     : https://prove2.me/submissions/6f693f7c-6341-43a9-a6db-b72971efe46e

import Mathlib
import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Theorems.Thm_QuantumMaxCutEnergy_rank3_gaussian_rounding_distribution

open scoped BigOperators
open MeasureTheory

namespace QuantumMaxCutEnergy

variable {n : ℕ}

/-- Correlation of two Bloch vectors. -/
noncomputable def pairCorr (r : Fin n → Fin 3 → ℝ) (i j : Fin n) : ℝ :=
  ∑ a : Fin 3, r i a * r j a

lemma continuous_pairCorr (i j : Fin n) :
    Continuous fun r : Fin n → Fin 3 → ℝ => pairCorr r i j := by
  have hi : Continuous fun r : Fin n → Fin 3 → ℝ => r i := continuous_apply i
  have hj : Continuous fun r : Fin n → Fin 3 → ℝ => r j := continuous_apply j
  refine continuous_finsetSum _ fun a _ => ?_
  exact ((continuous_apply a).comp hi).mul ((continuous_apply a).comp hj)

lemma abs_pairCorr_le_one (r : Fin n → Fin 3 → ℝ)
    (hr : ∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) (i j : Fin n) : |pairCorr r i j| ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3))
    (fun a => r i a) (fun a => r j a)
  simp only [hr i, hr j, mul_one] at h
  have h2 : (pairCorr r i j) ^ 2 ≤ 1 := by simpa [pairCorr] using h
  rw [abs_le]
  constructor <;> nlinarith [h2, sq_nonneg (pairCorr r i j - 1), sq_nonneg (pairCorr r i j + 1)]

lemma integrable_pairCorr (μ : Measure (Fin n → Fin 3 → ℝ)) [IsProbabilityMeasure μ]
    (hunit : ∀ᵐ r ∂μ, ∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) (i j : Fin n) :
    Integrable (fun r => pairCorr r i j) μ := by
  refine Integrable.of_bound (continuous_pairCorr i j).aestronglyMeasurable 1 ?_
  filter_upwards [hunit] with r hr
  simpa [Real.norm_eq_abs] using abs_pairCorr_le_one r hr i j

/-- **The probabilistic method step.**  If a probability distribution on Bloch assignments
has pair correlations bounded by `0.046 + 0.954 * X i j` in mean, then some single
assignment satisfies the edge-wise inequality for every nonnegative weighting `w`. -/
lemma rounding_of_expectation_bound (w : Weights n) (X : Matrix (Fin n) (Fin n) ℝ)
    (μ : Measure (Fin n → Fin 3 → ℝ)) [IsProbabilityMeasure μ]
    (hunit : ∀ᵐ r ∂μ, ∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1)
    (hbound : ∀ i j : Fin n, ∫ r, pairCorr r i j ∂μ ≤ 0.046 + 0.954 * X i j) :
    ∃ r : Fin n → Fin 3 → ℝ, (∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) ∧
      ∑ e : Edge n, (w e : ℝ) * pairCorr r e.val.1 e.val.2 ≤
        0.046 * (∑ e : Edge n, (w e : ℝ)) + 0.954 * (∑ e : Edge n, (w e : ℝ) * X e.val.1 e.val.2) := by
  classical
  set F : (Fin n → Fin 3 → ℝ) → ℝ :=
    fun r => ∑ e : Edge n, (w e : ℝ) * pairCorr r e.val.1 e.val.2 with hF
  set B : ℝ := ∑ e : Edge n, (w e : ℝ) * (0.046 + 0.954 * X e.val.1 e.val.2) with hB
  have hBsplit : B = 0.046 * (∑ e : Edge n, (w e : ℝ)) +
      0.954 * (∑ e : Edge n, (w e : ℝ) * X e.val.1 e.val.2) := by
    rw [hB, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hFcont : Continuous F := by
    rw [hF]
    exact continuous_finsetSum _ fun e _ => (continuous_pairCorr _ _).const_mul _
  have hFint : Integrable F μ := by
    refine Integrable.of_bound hFcont.aestronglyMeasurable (∑ e : Edge n, (w e : ℝ)) ?_
    filter_upwards [hunit] with r hr
    rw [Real.norm_eq_abs, hF]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum fun e _ => ?_
    have hw : (0:ℝ) ≤ (w e : ℝ) := by positivity
    rw [abs_mul, abs_of_nonneg hw]
    calc (w e : ℝ) * |pairCorr r e.val.1 e.val.2| ≤ (w e : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (abs_pairCorr_le_one r hr _ _) hw
      _ = (w e : ℝ) := mul_one _
  have hIntF : ∫ r, F r ∂μ =
      ∑ e : Edge n, (w e : ℝ) * ∫ r, pairCorr r e.val.1 e.val.2 ∂μ := by
    rw [hF, integral_finsetSum Finset.univ
      (fun e _ => (integrable_pairCorr μ hunit _ _).const_mul _)]
    exact Finset.sum_congr rfl fun e _ => integral_const_mul _ _
  have hle : ∫ r, F r ∂μ ≤ B := by
    rw [hIntF, hB]
    refine Finset.sum_le_sum fun e _ => ?_
    exact mul_le_mul_of_nonneg_left (hbound _ _) (by positivity)
  by_contra hcon
  have hpoint : ∀ r, (∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) → B < F r := by
    intro r hr
    by_contra hle'
    exact hcon ⟨r, hr, by rw [← hBsplit]; exact not_lt.mp hle'⟩
  have hnull : μ {r : Fin n → Fin 3 → ℝ | ¬ (∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1)} = 0 := by
    rw [← MeasureTheory.ae_iff]
    exact hunit
  have hGmeas : Measurable fun r : Fin n → Fin 3 → ℝ => F r - B :=
    hFcont.measurable.sub measurable_const
  have hSmeas : MeasurableSet {r : Fin n → Fin 3 → ℝ | 0 < F r - B} :=
    measurableSet_lt measurable_const hGmeas
  have hScompl : μ {r : Fin n → Fin 3 → ℝ | 0 < F r - B}ᶜ = 0 := by
    refine MeasureTheory.measure_mono_null ?_ hnull
    intro r hr
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hr
    simp only [Set.mem_ofPred_eq]
    intro hu
    have := hpoint r hu
    linarith
  have hSprob : μ {r : Fin n → Fin 3 → ℝ | 0 < F r - B} = 1 := by
    have h := MeasureTheory.measure_add_measure_compl (μ := μ) hSmeas
    rw [hScompl, add_zero, MeasureTheory.measure_univ] at h
    exact h
  have hsupp : 0 < μ (Function.support fun r : Fin n → Fin 3 → ℝ => F r - B) := by
    have h₁ : μ {r : Fin n → Fin 3 → ℝ | 0 < F r - B} ≤
        μ (Function.support fun r : Fin n → Fin 3 → ℝ => F r - B) := by
      refine MeasureTheory.measure_mono ?_
      intro r hr
      simp only [Set.mem_ofPred_eq] at hr
      simp only [Function.mem_support, ne_eq]
      linarith
    rw [hSprob] at h₁
    exact lt_of_lt_of_le one_pos h₁
  have hGnonneg : 0 ≤ᵐ[μ] fun r : Fin n → Fin 3 → ℝ => F r - B := by
    filter_upwards [hunit] with r hr
    have h2 := hpoint r hr
    show (0:ℝ) ≤ F r - B
    linarith
  have hGint : Integrable (fun r : Fin n → Fin 3 → ℝ => F r - B) μ :=
    hFint.sub (integrable_const B)
  have hpos : 0 < ∫ r, (F r - B) ∂μ := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg_ae hGnonneg hGint]
    exact hsupp
  have hBint : ∫ r : Fin n → Fin 3 → ℝ, B ∂μ = B := by
    rw [MeasureTheory.integral_const, MeasureTheory.Measure.real_def, MeasureTheory.measure_univ]
    simp
  rw [MeasureTheory.integral_sub hFint (integrable_const B), hBint] at hpos
  linarith

end QuantumMaxCutEnergy

theorem solution (n : ℕ) (w : QuantumMaxCutEnergy.Weights n) (X : Matrix (Fin n) (Fin n) ℝ)
    (hX : X.PosSemidef) (hdiag : ∀ i, X i i = 1) :
    ∃ r : Fin n → Fin 3 → ℝ,
      (∀ i, ∑ a : Fin 3, (r i a) ^ 2 = 1) ∧
      (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) *
          (∑ a : Fin 3, r e.val.1 a * r e.val.2 a)) ≤
        0.046 * (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ)) +
          0.954 * (∑ e : QuantumMaxCutEnergy.Edge n, (w e : ℝ) * X e.val.1 e.val.2) := by
  obtain ⟨μ, hμ, hunit, hbound⟩ :=
    QuantumMaxCutEnergy.rank3_gaussian_rounding_distribution n X hX hdiag
  simpa [QuantumMaxCutEnergy.pairCorr] using
    @QuantumMaxCutEnergy.rounding_of_expectation_bound n w X μ hμ hunit hbound
