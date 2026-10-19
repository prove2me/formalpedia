-- Prove2me | solution 1 for QuantumMC.MeanEst.theorem_5_l2_bound
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T18:08:49.842821+00:00
-- url     : https://prove2.me/submissions/88ce9894-e7bf-4610-b98c-d162c860ffd9

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

open MeasureTheory ProbabilityTheory Filter
set_option linter.unusedVariables false

open QuantumMC.MeanEst

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hXm : Measurable X)
    (hX : MemLp X 2 P) (σ : ℝ) (hvar : variance X P ≤ σ ^ 2)
    (hσ : 0 < σ) (m : ℝ) (hm : |m - ∫ x, X x / σ ∂P| ≤ 3) :
    l2norm P (alg3B σ m X) ≤ 4 := by
  set Y : Ω → ℝ := fun ω => X ω / σ with hYdef
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hYmem : MemLp Y 2 P := by
    have : Y = fun ω => X ω * σ⁻¹ := by
      funext ω; rw [hYdef]; simp [div_eq_mul_inv]
    rw [this]; exact hX.mul_const σ⁻¹
  have hYint : Integrable Y P := hYmem.integrable (by norm_num)
  set c : ℝ := P[Y] - m with hcdef
  -- variance of Y is at most 1
  have hvarY : variance Y P ≤ 1 := by
    have hYeq : Y = fun ω => X ω * σ⁻¹ := by
      funext ω; rw [hYdef]; simp [div_eq_mul_inv]
    rw [hYeq, variance_mul_const]
    have hσ2 : (0 : ℝ) ≤ σ⁻¹ ^ 2 := sq_nonneg _
    have h1 : σ ^ 2 * σ⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hσne, one_pow]
    calc variance X P * σ⁻¹ ^ 2 ≤ σ ^ 2 * σ⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right hvar hσ2
      _ = 1 := h1
  -- the L² norm of the shift is ∫ (Y - m)² = variance Y + c²
  have hYsub2 : (∫ ω, (Y ω - m) ^ 2 ∂P) = variance Y P + c ^ 2 := by
    have hd : Integrable (fun ω => (Y ω - P[Y]) ^ 2) P :=
      (hYmem.sub (memLp_const (P[Y]))).integrable_sq
    have hco : (∫ ω, (Y ω - P[Y]) ^ 2 ∂P) = variance Y P :=
      (variance_eq_integral hYmem.aemeasurable).symm
    have hlin : (∫ ω, (Y ω - P[Y]) ∂P) = 0 := by
      rw [integral_sub hYint (integrable_const _), integral_const]
      simp [Measure.real, measure_univ]
    have hBd : Integrable (fun ω => (2 * (P[Y] - m)) * (Y ω - P[Y])) P :=
      (hYint.sub (integrable_const _)).const_mul _
    have hCd : Integrable (fun _ : Ω => (P[Y] - m) ^ 2) P := integrable_const _
    calc ∫ ω, (Y ω - m) ^ 2 ∂P
        = ∫ ω, ((Y ω - P[Y]) ^ 2 + (2 * (P[Y] - m)) * (Y ω - P[Y]))
            + (P[Y] - m) ^ 2 ∂P :=
          integral_congr_ae (Eventually.of_forall (fun ω => by ring))
      _ = (∫ ω, (Y ω - P[Y]) ^ 2 + (2 * (P[Y] - m)) * (Y ω - P[Y]) ∂P)
            + (∫ _ : Ω, (P[Y] - m) ^ 2 ∂P) := by
          simpa using integral_add (hd.add hBd) hCd
      _ = ((∫ ω, (Y ω - P[Y]) ^ 2 ∂P)
            + (∫ ω, (2 * (P[Y] - m)) * (Y ω - P[Y]) ∂P))
            + (∫ _ : Ω, (P[Y] - m) ^ 2 ∂P) := by
          rw [integral_add hd hBd]
      _ = variance Y P + c ^ 2 := by
          rw [hco, integral_const_mul, hlin, integral_const]
          simp only [Measure.real, measure_univ, ENNReal.toReal_one, mul_zero, add_zero, one_smul]
          rw [hcdef]
  -- bound the shift
  have hc_bound : c ^ 2 ≤ 9 := by
    have habs : |c| ≤ 3 := by
      rw [hcdef]
      have hYeq : ∫ x, X x / σ ∂P = P[Y] := by simp only [hYdef]
      rw [hYeq] at hm
      calc |P[Y] - m| = |m - P[Y]| := abs_sub_comm _ _
        _ ≤ 3 := hm
    nlinarith [abs_nonneg c, sq_abs c, habs]
  have htotal : (∫ ω, (Y ω - m) ^ 2 ∂P) ≤ 10 := by
    rw [hYsub2]; linarith
  have hnorm : l2norm P (alg3B σ m X) = Real.sqrt (∫ ω, (Y ω - m) ^ 2 ∂P) := by
    have hB : alg3B σ m X = fun ω => Y ω - m := rfl
    rw [hB, l2norm]
  rw [hnorm]
  calc Real.sqrt (∫ ω, (Y ω - m) ^ 2 ∂P)
      ≤ Real.sqrt 10 := Real.sqrt_le_sqrt htotal
    _ ≤ 4 := by
        rw [Real.sqrt_le_iff]
        constructor <;> norm_num
