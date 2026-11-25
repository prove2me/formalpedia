-- Prove2me | solution 1 for PositivityTheory.ThKF0.Grow.oneD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:03:08.146943+00:00
-- url     : https://prove2.me/submissions/9a864b21-58dc-4c1f-8f20-04993842fd28

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LeviDeterminants_GrowSobA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF0 PositivityTheory.ThKF0.Grow
open scoped ENNReal
open MeasureTheory
namespace PositivityTheory.ThKF0.Grow
theorem _root_.solution (u u' : ℝ → ℂ) (hu' : Continuous u') (h : ∀ t, HasDerivAt u (u' t) t) :
    ‖u 0‖ₑ ^ 2 ≤ 2 * ∫⁻ t, (‖u t‖ₑ ^ 2 + ‖u' t‖ₑ ^ 2) := by
  have hu : Continuous u := continuous_iff_continuousAt.2 fun t => (h t).continuousAt
  have hd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ((s : ℂ) - 1) * u s ^ 2) (u t ^ 2 + ((t : ℂ) - 1) * (2 * u t * u' t)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) - 1) 1 t := (Complex.ofRealCLM.hasDerivAt (x := t)).sub_const 1
    have h2 : HasDerivAt (fun s : ℝ => u s ^ 2) (2 * u t * u' t) t := by
      simpa using (h t).fun_pow 2
    simpa using h1.fun_mul h2
  have hc : Continuous fun t : ℝ => u t ^ 2 + ((t : ℂ) - 1) * (2 * u t * u' t) := by fun_prop
  have e := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun t _ => hd t) (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le zero_le_one] at e
  have e' : u 0 ^ 2 = ∫ t in Set.Ioc (0 : ℝ) 1, (u t ^ 2 + ((t : ℂ) - 1) * (2 * u t * u' t)) := by
    rw [e]; simp
  rw [← enorm_pow, e', ← lintegral_const_mul' _ _ (by simp)]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  refine le_trans (setLIntegral_mono' measurableSet_Ioc fun t ht => ?_) (setLIntegral_le_lintegral _ _)
  have h1 : ‖(t : ℂ) - 1‖ ≤ 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h2 : ‖u t ^ 2 + ((t : ℂ) - 1) * (2 * u t * u' t)‖ ≤ 2 * (‖u t‖ ^ 2 + ‖u' t‖ ^ 2) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_two]
    have : ‖(t : ℂ) - 1‖ * (2 * ‖u t‖ * ‖u' t‖) ≤ 1 * (2 * ‖u t‖ * ‖u' t‖) := by gcongr
    nlinarith [sq_nonneg (‖u t‖ - ‖u' t‖), sq_nonneg ‖u' t‖]
  rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_ofNat,
    ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal h2
end PositivityTheory.ThKF0.Grow
