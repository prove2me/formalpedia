-- Prove2me | solution 1 for Section5FiniteProbability.exponential_moment_of_tail
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:19:54.375321+00:00
-- url     : https://prove2.me/submissions/498230b2-ceb7-49d8-b968-0353f4d34b5a

import Mathlib
set_option autoImplicit false
namespace Section5FiniteProbability
end Section5FiniteProbability
open Section5FiniteProbability
open MeasureTheory Set
theorem solution {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : ∀ x, 0 ≤ Y x)
    (htail : ∀ t : ℝ, 0 ≤ t → μ.real {x | t ≤ Y x} ≤ 3*Real.exp (-t/4)) :
    (∫ x, Real.exp (Y x/512) ∂μ) ≤ 130/127 := by
  have hprimitive (y : ℝ) :
      (∫ t in 0..y, Real.exp (t/512)/512)=Real.exp (y/512)-1 := by
    rw [intervalIntegral.integral_div,
      intervalIntegral.integral_comp_div Real.exp (by norm_num : (512 : ℝ) ≠ 0)]
    simp only [integral_exp,zero_div,Real.exp_zero,smul_eq_mul]
    ring
  have hkey := lintegral_comp_eq_lintegral_meas_le_mul μ
    (ae_of_all _ hY) (measurable_of_finite Y).aemeasurable
    (fun t _ => (show Continuous (fun s : ℝ => Real.exp (s/512)/512) by fun_prop).intervalIntegrable 0 t)
    (ae_of_all _ (fun t : ℝ => (by positivity : 0 ≤ Real.exp (t/512)/512)))
  simp only [hprimitive] at hkey
  have hdom : IntegrableOn (fun t : ℝ => (3/512)*Real.exp ((-127/512)*t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-127/512 : ℝ) < 0) 0).const_mul _
  have hbound : ENNReal.ofReal (∫ x, (Real.exp (Y x/512)-1) ∂μ) ≤
      ENNReal.ofReal (3/127) := by
    have hnonneg : ∀ x, 0 ≤ Real.exp (Y x/512)-1 := by
      intro x
      exact sub_nonneg.mpr (Real.one_le_exp (div_nonneg (hY x) (by norm_num)))
    rw [ofReal_integral_eq_lintegral_ofReal (Integrable.of_finite) (ae_of_all _ hnonneg),hkey]
    calc
      _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((3/512)*Real.exp ((-127/512)*t)) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have hprob : μ {x | t ≤ Y x} ≤ ENNReal.ofReal (3*Real.exp (-t/4)) := by
          have he := ENNReal.ofReal_le_ofReal (htail t ht.le)
          simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top μ _)] using he
        calc
          _ ≤ ENNReal.ofReal (3*Real.exp (-t/4))*ENNReal.ofReal (Real.exp (t/512)/512) :=
            mul_le_mul_of_nonneg_right hprob (by positivity)
          _ = _ := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [show 3*Real.exp (-t/4)*(Real.exp (t/512)/512)=
              (3/512)*(Real.exp (-t/4)*Real.exp (t/512)) by ring,← Real.exp_add]
            congr 2
            ring
      _ = ENNReal.ofReal (∫ t : ℝ in Ioi 0, (3/512)*Real.exp ((-127/512)*t)) :=
        (ofReal_integral_eq_lintegral_ofReal hdom (ae_of_all _ (fun t => by positivity))).symm
      _ = ENNReal.ofReal (3/127) := by
        rw [integral_const_mul,integral_exp_mul_Ioi (by norm_num : (-127/512 : ℝ) < 0) 0]
        norm_num
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 3/127)).mp hbound
  rw [integral_sub (Integrable.of_finite) (integrable_const (1 : ℝ)),integral_const] at hreal
  simp only [smul_eq_mul,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] at hreal
  linarith
