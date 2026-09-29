-- Prove2me | solution 1 for PreorderADI.Correlation.availability_eq_expectation
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:16:43.459144+00:00
-- url     : https://prove2.me/submissions/af270d49-c516-49d0-8edf-0d302c550d22

import Mathlib
import Definitions.Def_PreorderADI_Correlation_Model

open MeasureTheory ProbabilityTheory

namespace PreorderADI.Correlation

theorem aux_avex_gauss_eq (m s : ℝ) :
    gaussianReal m (Real.toNNReal (s ^ 2)) = (gaussianReal 0 1).map (fun z => s * z + m) := by
  have h1 : (gaussianReal 0 1).map (fun z => s * z + m)
      = ((gaussianReal 0 1).map (s * ·)).map (· + m) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [h1, gaussianReal_map_const_mul, gaussianReal_map_add_const]
  congr 1
  · ring
  · ext
    simp [Real.coe_toNNReal _ (sq_nonneg s)]

theorem aux_avex_point (P : Params) (hP : P.Standing) (ρ : ℝ) (hρ : ρ ∈ Set.Ico (0:ℝ) 1)
    (x : ℝ) :
    (lowDemandLaw P ρ x).real {y | y / 2 < orderQty P ρ x} =
      stdNormalCdf ((P.lamL + ρ * x) / Real.sqrt (1 - ρ ^ 2) + 2 * P.zL) := by
  have hsq : 0 < Real.sqrt (1 - ρ ^ 2) := Real.sqrt_pos.2 (by nlinarith [hρ.1, hρ.2])
  have hs : 0 < lowSd P ρ := mul_pos hP.sigmaL_pos hsq
  have hpre : (fun z => lowSd P ρ * z + lowMean P ρ x) ⁻¹' {y | y / 2 < orderQty P ρ x}
      = Set.Iio (lowMean P ρ x / lowSd P ρ + 2 * P.zL) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Iio, orderQty]
    rw [div_add' _ _ _ hs.ne', lt_div_iff₀ hs]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  unfold lowDemandLaw
  rw [aux_avex_gauss_eq (lowMean P ρ x) (lowSd P ρ),
    map_measureReal_apply (by fun_prop) (measurableSet_lt (by fun_prop) measurable_const), hpre]
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  rw [measureReal_congr Iio_ae_eq_Iic, stdNormalCdf, cdf_eq_real]
  congr 3
  rw [lowMean, lowSd, Params.lamL]
  have := hP.sigmaL_pos
  field_simp

end PreorderADI.Correlation

open PreorderADI.Correlation

theorem solution (P : Params) (hP : P.Standing)
    (ρ : ℝ) (hρ : ρ ∈ Set.Ico (0:ℝ) 1) :
    (∀ x : ℝ, (lowDemandLaw P ρ x).real {y | y / 2 < orderQty P ρ x} =
      stdNormalCdf ((P.lamL + ρ * x) / Real.sqrt (1 - ρ ^ 2) + 2 * P.zL)) ∧
    availability P ρ =
      ∫ x, stdNormalCdf ((P.lamL + ρ * x) / Real.sqrt (1 - ρ ^ 2) + 2 * P.zL)
        ∂(gaussianReal 0 1) := by
  refine ⟨fun x => aux_avex_point P hP ρ hρ x, ?_⟩
  unfold availability
  congr 1
  funext x
  exact aux_avex_point P hP ρ hρ x
