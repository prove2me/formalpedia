-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_lintegral_abs_log_circle_le_d71509c99c48
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:03:21.186364+00:00
-- url     : https://prove2.me/submissions/2f9c65f3-1066-41e3-8fdc-ebd68a11263b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntCircle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Set
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (P : Polynomial ℂ) (D d0 : ℕ) (M : ℝ)
    (hD : P.natDegree ≤ D) (hd0 : P.coeff d0 ≠ 0)
    (hM : ∀ θ : ℝ, ‖P.eval (circleMap 0 1 θ)‖ ≤ M) :
    ∫⁻ θ in Ioc 0 (2 * Real.pi), ‖Real.log ‖P.eval (circleMap 0 1 θ)‖‖ₑ ≤
      ENNReal.ofReal (4 * Real.pi * Real.log (max M 1) + 2 * Real.pi * D * Real.log 2 +
        2 * Real.pi * |Real.log ‖P.coeff d0‖|) := by
  set G : ℝ → ℝ := fun θ => Real.log ‖P.eval (circleMap 0 1 θ)‖ with hGdef
  have hP : P ≠ 0 := fun h => hd0 (by simp [h])
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hii : IntervalIntegrable G volume 0 (2 * Real.pi) := Polynomial.intervalIntegrable_mahlerMeasure P
  have hint : IntegrableOn G (Ioc 0 (2 * Real.pi)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h2pi).mp hii
  rw [← ofReal_integral_norm_eq_lintegral_enorm hint]
  apply ENNReal.ofReal_le_ofReal
  set L := Real.log (max M 1) with hL
  have hpos : ∀ θ, G θ ≤ L := by
    intro θ
    by_cases h0 : ‖P.eval (circleMap 0 1 θ)‖ = 0
    · simp only [hGdef, h0, Real.log_zero]; exact Real.log_nonneg (le_max_right _ _)
    · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))
        ((hM θ).trans (le_max_left _ _))
  have hnorm : ∀ θ, ‖G θ‖ = 2 * max (G θ) 0 - G θ := by
    intro θ; rw [Real.norm_eq_abs]; rcases le_total (G θ) 0 with h | h
    · rw [abs_of_nonpos h, max_eq_right h]; ring
    · rw [abs_of_nonneg h, max_eq_left h]; ring
  have hmaxint : IntegrableOn (fun θ => max (G θ) 0) (Ioc 0 (2 * Real.pi)) := hint.pos_part
  have e1 : ∫ θ in Ioc 0 (2 * Real.pi), ‖G θ‖ =
      2 * (∫ θ in Ioc 0 (2 * Real.pi), max (G θ) 0) - ∫ θ in Ioc 0 (2 * Real.pi), G θ := by
    rw [show (fun θ => ‖G θ‖) = fun θ => 2 * max (G θ) 0 - G θ from funext hnorm]
    rw [integral_sub (hmaxint.const_mul 2) hint, integral_const_mul]
  have e2 : ∫ θ in Ioc 0 (2 * Real.pi), max (G θ) 0 ≤ 2 * Real.pi * L := by
    have : ∫ θ in Ioc 0 (2 * Real.pi), max (G θ) 0 ≤ ∫ θ in Ioc 0 (2 * Real.pi), L := by
      refine setIntegral_mono_on hmaxint (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc ?_
      intro θ _
      exact max_le (hpos θ) (Real.log_nonneg (le_max_right _ _))
    refine this.trans (le_of_eq ?_)
    rw [setIntegral_const]
    simp [Measure.real, Real.volume_Ioc, Real.pi_pos.le, smul_eq_mul]
  have e3 : ∫ θ in Ioc 0 (2 * Real.pi), G θ = 2 * Real.pi * P.logMahlerMeasure := by
    rw [Polynomial.logMahlerMeasure_def, Real.circleAverage_def, ← intervalIntegral.integral_of_le h2pi]
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have e4 : Real.log ‖P.coeff d0‖ - D * Real.log 2 ≤ P.logMahlerMeasure := by
    have hc := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure d0 P
    have hm := Polynomial.mahlerMeasure_pos_of_ne_zero hP
    have hch : ((P.natDegree.choose d0 : ℕ) : ℝ) ≤ 2 ^ D := by
      have := (Nat.choose_le_two_pow P.natDegree d0).trans (Nat.pow_le_pow_right (by norm_num) hD)
      exact_mod_cast this
    have h1 : ‖P.coeff d0‖ ≤ 2 ^ D * P.mahlerMeasure :=
      hc.trans (mul_le_mul_of_nonneg_right hch hm.le)
    have h2 := Real.log_le_log (norm_pos_iff.mpr hd0) h1
    rw [Real.log_mul (by positivity) hm.ne', Real.log_pow] at h2
    rw [Polynomial.logMahlerMeasure_eq_log_MahlerMeasure]
    linarith
  rw [e1, e3]
  have h5 := neg_abs_le (Real.log ‖P.coeff d0‖)
  have h6 := mul_le_mul_of_nonneg_left e4 h2pi
  have h7 := mul_le_mul_of_nonneg_left h5 h2pi
  linarith [e2, h6, h7]
end GroundTheory.Heights₂.Heights.LogInt
