-- Prove2me | solution 1 for QuantumMC.MeanEst.theorem_5_chebyshev
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T18:08:49.139775+00:00
-- url     : https://prove2.me/submissions/0a4020a6-7af5-4672-907f-5bc3767fdf9d

import Mathlib
import Definitions.Def_QuantumMC_MeanEst_Setting

open MeasureTheory ProbabilityTheory Filter
set_option linter.unusedVariables false

open QuantumMC.MeanEst

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → ℝ) (hXm : Measurable X)
    (hX : MemLp X 2 P) (σ : ℝ) (hvar : variance X P ≤ σ ^ 2)
    (hσ : 0 < σ) :
    P {ω | 3 ≤ |X ω / σ - ∫ x, X x / σ ∂P|} ≤ (1 / 9 : ENNReal) := by
  set Y : Ω → ℝ := fun ω => X ω / σ with hYdef
  have hσne : σ ≠ 0 := ne_of_gt hσ
  have hYmem : MemLp Y 2 P := by
    have : Y = fun ω => X ω * σ⁻¹ := by
      funext ω; rw [hYdef]; simp [div_eq_mul_inv]
    rw [this]; exact hX.mul_const σ⁻¹
  -- variance of Y is at most 1
  have hvarY : variance Y P ≤ 1 := by
    have hYeq : Y = fun ω => X ω * σ⁻¹ := by
      funext ω; rw [hYdef]; simp [div_eq_mul_inv]
    rw [hYeq, variance_mul_const]
    have hσ2 : (0 : ℝ) ≤ σ⁻¹ ^ 2 := sq_nonneg _
    have : σ ^ 2 * σ⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hσne, one_pow]
    calc variance X P * σ⁻¹ ^ 2 ≤ σ ^ 2 * σ⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right hvar hσ2
      _ = 1 := this
  have hint : ∫ x, X x / σ ∂P = P[Y] := by
    simp only [hYdef]
  rw [hint]
  have hcheb := meas_ge_le_variance_div_sq (μ := P) hYmem (c := (3 : ℝ)) (by norm_num)
  refine hcheb.trans ?_
  have hbound : variance Y P / 3 ^ 2 ≤ (1 / 9 : ℝ) := by
    nlinarith [hvarY]
  calc ENNReal.ofReal (variance Y P / 3 ^ 2)
      ≤ ENNReal.ofReal (1 / 9 : ℝ) := ENNReal.ofReal_le_ofReal hbound
    _ = (1 / 9 : ENNReal) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 9)]
        norm_num
