-- Prove2me | solution 1 for UnbiasedTimeAvg.eq_H_3
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T04:25:39.386465+00:00
-- url     : https://prove2.me/submissions/fce450df-c7b1-4d8d-acdb-558be94c1787

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal ProbabilityTheory

theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (V₁ V₂ Q : Ω → ℝ) (q : ℝ) (hq : 0 < q)
    (hV₁ : MemLp V₁ 2 P) (hV₂ : MemLp V₂ 2 P) (hV_indep : IndepFun V₁ V₂ P)
    (hQ_meas : Measurable Q) (hQ_bin : ∀ ω, Q ω = 0 ∨ Q ω = 1)
    (hQ_law : P {ω | Q ω = 1} = ENNReal.ofReal q)
    (hQ_indep : IndepFun Q (fun ω => (V₁ ω, V₂ ω)) P) :
    MemLp (fun ω => V₁ ω + q⁻¹ * Q ω * V₂ ω) 2 P ∧
    variance (fun ω => V₁ ω + q⁻¹ * Q ω * V₂ ω) P
      = variance V₁ P + q⁻¹ ^ 2 * variance (fun ω => Q ω * V₂ ω) P ∧
    variance (fun ω => V₁ ω + q⁻¹ * Q ω * V₂ ω) P
      ≤ variance V₁ P + q⁻¹ * ∫ ω, V₂ ω ^ 2 ∂P := by
  have hq' : q ≠ 0 := hq.ne'
  -- E[Q] = q
  have hQ_int : ∫ ω, Q ω ∂P = q := by
    have h1 : Q = {ω | Q ω = 1}.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      rcases hQ_bin ω with h | h <;> simp [h]
    rw [h1, integral_indicator (s := {ω | Q ω = 1})
      (show MeasurableSet {ω | Q ω = 1} from hQ_meas (measurableSet_singleton 1)), setIntegral_const]
    rw [measureReal_def, hQ_law, ENNReal.toReal_ofReal hq.le]
    simp only [smul_eq_mul, mul_one]
  have hQ_abs : ∀ ω, |Q ω| ≤ 1 := by
    intro ω; rcases hQ_bin ω with h | h <;> simp [h]
  -- MemLp of Q * V₂ and of Y
  have hQV2_meas : AEStronglyMeasurable (fun ω => Q ω * V₂ ω) P :=
    hQ_meas.aestronglyMeasurable.mul hV₂.aestronglyMeasurable
  have hQV2 : MemLp (fun ω => Q ω * V₂ ω) 2 P := by
    refine MemLp.of_le hV₂ hQV2_meas ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    calc |Q ω| * |V₂ ω| ≤ 1 * |V₂ ω| := by
          gcongr
          exact hQ_abs ω
      _ = |V₂ ω| := one_mul _
  have hY : MemLp (fun ω => q⁻¹ * Q ω * V₂ ω) 2 P := by
    have h := hQV2.const_mul q⁻¹
    simpa only [mul_assoc] using h
  -- independence computations
  have hind_QV2 : IndepFun Q V₂ P := by
    have h := hQ_indep.comp measurable_id measurable_snd
    exact h
  have hind_QV1V2 : IndepFun Q (fun ω => V₁ ω * V₂ ω) P := by
    have hφ : Measurable (fun p : ℝ × ℝ => p.1 * p.2) := by fun_prop
    have h := hQ_indep.comp measurable_id hφ
    exact h
  have hind_QV2sq : IndepFun Q (fun ω => V₂ ω ^ 2) P := by
    have hφ : Measurable (fun p : ℝ × ℝ => p.2 ^ 2) := by fun_prop
    have h := hQ_indep.comp measurable_id hφ
    exact h
  have hV1V2_int : ∫ ω, V₁ ω * V₂ ω ∂P = (∫ ω, V₁ ω ∂P) * (∫ ω, V₂ ω ∂P) := by
    have h := hV_indep.integral_mul_eq_mul_integral hV₁.aestronglyMeasurable hV₂.aestronglyMeasurable
    simpa only [Pi.mul_apply] using h
  have hQV2_int : ∫ ω, Q ω * V₂ ω ∂P = q * ∫ ω, V₂ ω ∂P := by
    have h := hind_QV2.integral_mul_eq_mul_integral hQ_meas.aestronglyMeasurable hV₂.aestronglyMeasurable
    simpa only [Pi.mul_apply, hQ_int] using h
  have hQ_V1V2_int : ∫ ω, Q ω * (V₁ ω * V₂ ω) ∂P =
      q * ((∫ ω, V₁ ω ∂P) * (∫ ω, V₂ ω ∂P)) := by
    have h := hind_QV1V2.integral_mul_eq_mul_integral hQ_meas.aestronglyMeasurable
      (hV₁.aestronglyMeasurable.mul hV₂.aestronglyMeasurable)
    simpa only [Pi.mul_apply, hQ_int, hV1V2_int] using h
  -- covariance vanishes
  have hcov : cov[V₁, fun ω => q⁻¹ * Q ω * V₂ ω; P] = 0 := by
    rw [covariance_eq_sub hV₁ hY]
    have e1 : ∫ ω, V₁ ω * (q⁻¹ * Q ω * V₂ ω) ∂P =
        q⁻¹ * ∫ ω, Q ω * (V₁ ω * V₂ ω) ∂P := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      ring
    have e2 : ∫ ω, (q⁻¹ * Q ω * V₂ ω) ∂P = q⁻¹ * ∫ ω, Q ω * V₂ ω ∂P := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ω
      ring
    have hmain : ∫ ω, V₁ ω * (q⁻¹ * Q ω * V₂ ω) ∂P =
        (∫ ω, V₁ ω ∂P) * (∫ ω, (q⁻¹ * Q ω * V₂ ω) ∂P) := by
      rw [e1, e2, hQ_V1V2_int, hQV2_int]
      field_simp
    simp only [Pi.mul_apply] at hmain ⊢
    linarith
  -- variance of Y
  have hvarY' : variance (fun ω => q⁻¹ * Q ω * V₂ ω) P =
      q⁻¹ ^ 2 * variance (fun ω => Q ω * V₂ ω) P := by
    have h := variance_const_mul (q⁻¹) (fun ω => Q ω * V₂ ω) P
    rw [show (fun ω => q⁻¹ * Q ω * V₂ ω) = (fun ω => q⁻¹ * (Q ω * V₂ ω)) from by
      funext ω; ring]
    exact h
  -- variance decomposition
  have hvarY : variance (fun ω => V₁ ω + q⁻¹ * Q ω * V₂ ω) P =
      variance V₁ P + 2 * cov[V₁, fun ω => q⁻¹ * Q ω * V₂ ω; P] +
        variance (fun ω => q⁻¹ * Q ω * V₂ ω) P := by
    have h := variance_add hV₁ hY
    rw [show (fun ω => V₁ ω + q⁻¹ * Q ω * V₂ ω) =
        (V₁ + fun ω => q⁻¹ * Q ω * V₂ ω) from by
      funext ω; simp [Pi.add_apply]]
    exact h
  -- bound on Var(Q V₂)
  have hbound : variance (fun ω => q⁻¹ * Q ω * V₂ ω) P ≤ q⁻¹ * ∫ ω, V₂ ω ^ 2 ∂P := by
    rw [hvarY']
    have hvle : variance (fun ω => Q ω * V₂ ω) P ≤ ∫ ω, (Q ω * V₂ ω) ^ 2 ∂P :=
      variance_le_expectation_sq hQV2_meas
    have hsq : ∫ ω, (Q ω * V₂ ω) ^ 2 ∂P = ∫ ω, Q ω * V₂ ω ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      rcases hQ_bin ω with h | h <;> simp [h]
    have hQV2sq_int : ∫ ω, Q ω * V₂ ω ^ 2 ∂P = q * ∫ ω, V₂ ω ^ 2 ∂P := by
      have h := hind_QV2sq.integral_mul_eq_mul_integral hQ_meas.aestronglyMeasurable
        (hV₂.aestronglyMeasurable.pow 2)
      simpa only [Pi.mul_apply, Pi.pow_apply, hQ_int] using h
    have hmain : variance (fun ω => Q ω * V₂ ω) P ≤ q * ∫ ω, V₂ ω ^ 2 ∂P := by
      rw [hsq, hQV2sq_int] at hvle
      exact hvle
    calc q⁻¹ ^ 2 * variance (fun ω => Q ω * V₂ ω) P
        ≤ q⁻¹ ^ 2 * (q * ∫ ω, V₂ ω ^ 2 ∂P) := by
          apply mul_le_mul_of_nonneg_left hmain
          positivity
      _ = q⁻¹ * ∫ ω, V₂ ω ^ 2 ∂P := by
          field_simp
  refine ⟨hV₁.add hY, ?_, ?_⟩
  · rw [hvarY, hcov, hvarY']
    ring
  · rw [hvarY, hcov, hvarY']
    linarith
