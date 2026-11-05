-- Prove2me | solution 1 for ProbabilityTheory.eLpNorm_sq_bandFun
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:41:45.763237+00:00
-- url     : https://prove2.me/submissions/f1d39863-437d-4d16-a16c-df76a8c4f2ae

import Definitions.Def_LeanLevy_RandomMeasure_TimeSpacePoisson
import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

theorem solution {ν : Measure ℝ} [SigmaFinite ν] {C : Set ℝ}
    (hC : MeasurableSet C) (s t : ℝ) :
    (eLpNorm ((Set.Ioc s t ×ˢ C).indicator fun p : ℝ × ℝ => p.2) 2 (volume.prod ν)) ^ 2
      = ENNReal.ofReal (t - s) * ∫⁻ x in C, ENNReal.ofReal (x ^ 2) ∂ν := by
  have hnorm :
      (eLpNorm ((Set.Ioc s t ×ˢ C).indicator fun p : ℝ × ℝ => p.2) 2 (volume.prod ν)) ^ 2
        = ∫⁻ p, ‖(Set.Ioc s t ×ˢ C).indicator (fun q : ℝ × ℝ => q.2) p‖ₑ ^ (2 : ℝ)
            ∂(volume.prod ν) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      show ((2 : ℝ≥0∞).toReal) = (2 : ℝ) from by norm_num,
      ← ENNReal.rpow_natCast (_ ^ (1 / (2 : ℝ))) 2, ← ENNReal.rpow_mul,
      show (1 / (2 : ℝ)) * ((2 : ℕ) : ℝ) = 1 from by norm_num, ENNReal.rpow_one]
  have hband :
      ∫⁻ p, ‖(Set.Ioc s t ×ˢ C).indicator (fun q : ℝ × ℝ => q.2) p‖ₑ ^ (2 : ℝ)
          ∂(volume.prod ν)
        = ∫⁻ p in Set.Ioc s t ×ˢ C, ENNReal.ofReal (p.2 ^ 2) ∂(volume.prod ν) := by
    rw [← lintegral_indicator (measurableSet_Ioc.prod hC)]
    refine lintegral_congr fun p => ?_
    by_cases hp : p ∈ Set.Ioc s t ×ˢ C
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Real.enorm_eq_ofReal_abs,
        ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
      congr 1
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, enorm_zero,
        ENNReal.zero_rpow_of_pos (by norm_num)]
  have htonelli :
      ∫⁻ p in Set.Ioc s t ×ˢ C, ENNReal.ofReal (p.2 ^ 2) ∂(volume.prod ν)
        = ENNReal.ofReal (t - s) * ∫⁻ x in C, ENNReal.ofReal (x ^ 2) ∂ν := by
    rw [← Measure.prod_restrict,
      lintegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ 2))
        (measurable_snd.pow_const 2).ennreal_ofReal.aemeasurable]
    have hinner : ∀ r : ℝ,
        ∫⁻ x, ENNReal.ofReal ((r, x).2 ^ 2) ∂(ν.restrict C)
          = ∫⁻ x in C, ENNReal.ofReal (x ^ 2) ∂ν := fun _ => rfl
    rw [lintegral_congr hinner, setLIntegral_const, Real.volume_Ioc, mul_comm]
  exact hnorm.trans (hband.trans htonelli)
