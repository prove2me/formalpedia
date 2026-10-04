-- Prove2me | solution 1 for TaoFivePrimes.eta0_fourier_decay_variation_source
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-09T14:23:45.591434+00:00
-- url     : https://prove2.me/submissions/5307a6ba-1089-4226-a7a7-21b2993ed92e

import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Mathlib

open MeasureTheory intervalIntegral

namespace TaoFivePrimes

/-- `log (1/2) = -log 2`, used to normalize the cutoff endpoints. -/
private lemma log_half_fd : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]

private lemma log_quarter_fd : Real.log (1 / 4 : ℝ) = -2 * Real.log 2 := by
  rw [show (1 / 4 : ℝ) = ((2 : ℝ)⁻¹) ^ 2 by norm_num,
    Real.log_pow, Real.log_inv]
  norm_num

private lemma eta0_eq_zero_of_le_fd {t : ℝ} (ht : t ≤ 1 / 4) : eta0 t = 0 := by
  unfold eta0
  split_ifs with hpos
  · have hlog : Real.log (2 * t) ≤ Real.log (1 / 2 : ℝ) := by
      exact Real.log_le_log (by positivity) (by linarith)
    rw [log_half_fd] at hlog
    have hneg : Real.log 2 ≤ -Real.log (2 * t) := by linarith
    have hcut : Real.log 2 - |Real.log (2 * t)| ≤ 0 :=
      sub_nonpos.mpr (hneg.trans (neg_le_abs (Real.log (2 * t))))
    rw [max_eq_left hcut, mul_zero]
  · rfl

private lemma eta0_eq_zero_of_ge_fd {t : ℝ} (ht : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  rw [if_pos (by linarith)]
  have hlog : Real.log 2 ≤ Real.log (2 * t) := by
    exact Real.log_le_log (by norm_num) (by linarith)
  have hcut : Real.log 2 - |Real.log (2 * t)| ≤ 0 :=
    sub_nonpos.mpr (hlog.trans (le_abs_self (Real.log (2 * t))))
  rw [max_eq_left hcut, mul_zero]

private lemma eta0_left_formula_fd {t : ℝ} (htlo : 1 / 4 ≤ t) (hthi : t ≤ 1 / 2) :
    eta0 t = 4 * (2 * Real.log 2 + Real.log t) := by
  unfold eta0
  rw [if_pos (by linarith), abs_of_nonpos]
  · rw [max_eq_right]
    · rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : t ≠ 0)]
      ring
    · have hlog : Real.log (1 / 2 : ℝ) ≤ Real.log (2 * t) := by
        exact Real.log_le_log (by norm_num) (by linarith)
      rw [log_half_fd] at hlog
      linarith
  · exact Real.log_nonpos (by positivity) (by linarith)

private lemma eta0_right_formula_fd {t : ℝ} (htlo : 1 / 2 ≤ t) (hthi : t ≤ 1) :
    eta0 t = -4 * Real.log t := by
  unfold eta0
  rw [if_pos (by linarith), abs_of_nonneg]
  · rw [max_eq_right]
    · rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by linarith : t ≠ 0)]
      ring
    · have hlog : Real.log (2 * t) ≤ Real.log 2 := by
        exact Real.log_le_log (by positivity) (by linarith)
      linarith
  · exact Real.log_nonneg (by linarith)

private lemma eta0_support_fd : Function.support eta0 ⊆ Set.Ioc (1 / 4) 1 := by
  intro t ht
  constructor
  · by_contra h
    exact ht (eta0_eq_zero_of_le_fd (le_of_not_gt h))
  · by_contra h
    exact ht (eta0_eq_zero_of_ge_fd (le_of_not_ge h))

/--
The specialization of Tao's Lemma 3.3 to the logarithmic cutoff `eta0`.
On `[1/4, 1/2]` its derivative is `4/t`, and on `[1/2, 1]` its derivative
is `-4/t`.  Integration by parts on the two intervals cancels the common
boundary term at `1/2`; their total derivative variation is `8 * log 2`.
-/
private theorem eta0_fourier_decay_variation_source_proof (u : ℝ) (hu : u ≠ 0) :
    norm (∫ t : ℝ, (eta0 t : ℂ) * expCircle (u * t)) ≤
      8 * Real.log 2 / (2 * Real.pi * |u|) := by
  let c : ℂ := (2 * Real.pi : ℝ) * Complex.I * u
  let E : ℝ → ℂ := fun t => Complex.exp (c * t)
  let V : ℝ → ℂ := fun t => E t / c
  let L : ℝ → ℂ := fun t => (4 * (2 * Real.log 2 + Real.log t) : ℝ)
  let R : ℝ → ℂ := fun t => (-4 * Real.log t : ℝ)
  let dL : ℝ → ℂ := fun t => (4 / t : ℝ)
  let dR : ℝ → ℂ := fun t => (-4 / t : ℝ)
  have hc : c ≠ 0 := by
    simp [c, Real.pi_ne_zero, hu]
  have hE_exp (t : ℝ) : E t = expCircle (u * t) := by
    dsimp [E, c, expCircle]
    congr 1
    push_cast
    ring
  have hEderiv (t : ℝ) : HasDerivAt E (c * E t) t := by
    have hinner : HasDerivAt (fun s : ℝ => c * (s : ℂ)) c t := by
      simpa using (hasDerivAt_id t).ofReal_comp.const_mul c
    have hexp := hinner.cexp
    dsimp [E] at hexp ⊢
    convert hexp using 1
    ring
  have hVderiv (t : ℝ) : HasDerivAt V (E t) t := by
    simpa [V, hc] using (hEderiv t).div_const c
  have hEcont : Continuous E := by
    rw [continuous_iff_continuousAt]
    exact fun t => (hEderiv t).continuousAt
  have hVcont : Continuous V := hEcont.div_const c
  have hLcont : ContinuousOn L (Set.uIcc (1 / 4 : ℝ) (1 / 2 : ℝ)) := by
    intro t ht
    have ht0 : t ≠ 0 := by norm_num [Set.uIcc] at ht; linarith
    have hr : HasDerivAt (fun s : ℝ => 4 * (2 * Real.log 2 + Real.log s))
        (4 / t) t := by
      simpa only [div_eq_mul_inv] using
        ((Real.hasDerivAt_log ht0).const_add (2 * Real.log 2)).const_mul 4
    exact hr.ofReal_comp.continuousAt.continuousWithinAt
  have hRcont : ContinuousOn R (Set.uIcc (1 / 2 : ℝ) 1) := by
    intro t ht
    have ht0 : t ≠ 0 := by norm_num [Set.uIcc] at ht; linarith
    have hr : HasDerivAt (fun s : ℝ => -4 * Real.log s) (-4 / t) t := by
      simpa only [div_eq_mul_inv] using
        (Real.hasDerivAt_log ht0).const_mul (-4)
    exact hr.ofReal_comp.continuousAt.continuousWithinAt
  have hdLcont : ContinuousOn dL (Set.uIcc (1 / 4 : ℝ) (1 / 2 : ℝ)) := by
    intro t ht
    have ht0 : t ≠ 0 := by norm_num [Set.uIcc] at ht; linarith
    have hr : ContinuousAt (fun s : ℝ => 4 / s) t :=
      continuousAt_const.div continuousAt_id ht0
    exact (Complex.continuous_ofReal.continuousAt.comp hr).continuousWithinAt
  have hdRcont : ContinuousOn dR (Set.uIcc (1 / 2 : ℝ) 1) := by
    intro t ht
    have ht0 : t ≠ 0 := by norm_num [Set.uIcc] at ht; linarith
    have hr : ContinuousAt (fun s : ℝ => -4 / s) t :=
      continuousAt_const.div continuousAt_id ht0
    exact (Complex.continuous_ofReal.continuousAt.comp hr).continuousWithinAt
  have hLderiv (t : ℝ) (ht : t ∈ Set.Ioo (min (1 / 4 : ℝ) (1 / 2))
      (max (1 / 4 : ℝ) (1 / 2))) : HasDerivAt L (dL t) t := by
    have ht0 : t ≠ 0 := by norm_num at ht; linarith
    have hr : HasDerivAt (fun s : ℝ => 4 * (2 * Real.log 2 + Real.log s))
        (4 / t) t := by
      simpa only [div_eq_mul_inv] using
        ((Real.hasDerivAt_log ht0).const_add (2 * Real.log 2)).const_mul 4
    simpa [L, dL] using hr.ofReal_comp
  have hRderiv (t : ℝ) (ht : t ∈ Set.Ioo (min (1 / 2 : ℝ) 1)
      (max (1 / 2 : ℝ) 1)) : HasDerivAt R (dR t) t := by
    have ht0 : t ≠ 0 := by norm_num at ht; linarith
    have hr : HasDerivAt (fun s : ℝ => -4 * Real.log s) (-4 / t) t := by
      simpa only [div_eq_mul_inv] using
        (Real.hasDerivAt_log ht0).const_mul (-4)
    simpa [R, dR] using hr.ofReal_comp
  have hEiL : IntervalIntegrable E volume (1 / 4 : ℝ) (1 / 2 : ℝ) :=
    hEcont.intervalIntegrable _ _
  have hEiR : IntervalIntegrable E volume (1 / 2 : ℝ) 1 :=
    hEcont.intervalIntegrable _ _
  have hdLi : IntervalIntegrable dL volume (1 / 4 : ℝ) (1 / 2 : ℝ) :=
    hdLcont.intervalIntegrable
  have hdRi : IntervalIntegrable dR volume (1 / 2 : ℝ) 1 :=
    hdRcont.intervalIntegrable
  have hleftIBP :
      (∫ t in (1 / 4 : ℝ)..(1 / 2 : ℝ), L t * E t) =
        L (1 / 2) * V (1 / 2) - L (1 / 4) * V (1 / 4) -
          ∫ t in (1 / 4 : ℝ)..(1 / 2 : ℝ), dL t * V t := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hLcont hVcont.continuousOn hLderiv
      (fun t _ => hVderiv t) hdLi hEiL
  have hrightIBP :
      (∫ t in (1 / 2 : ℝ)..1, R t * E t) =
        R 1 * V 1 - R (1 / 2) * V (1 / 2) -
          ∫ t in (1 / 2 : ℝ)..1, dR t * V t := by
    exact intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      hRcont hVcont.continuousOn hRderiv
      (fun t _ => hVderiv t) hdRi hEiR
  have hLzero : L (1 / 4) = 0 := by
    dsimp [L]
    rw [log_quarter_fd]
    push_cast
    ring
  have hRzero : R 1 = 0 := by simp [R]
  have hmid : L (1 / 2) = R (1 / 2) := by
    dsimp [L, R]
    rw [log_half_fd]
    push_cast
    ring
  have hpiece :
      (∫ t : ℝ, (eta0 t : ℂ) * E t) =
        -(∫ t in (1 / 4 : ℝ)..(1 / 2 : ℝ), dL t * V t) -
          (∫ t in (1 / 2 : ℝ)..1, dR t * V t) := by
    have hsupp : Function.support (fun t : ℝ => (eta0 t : ℂ) * E t) ⊆
        Set.Ioc (1 / 4) 1 := by
      intro t ht
      apply eta0_support_fd
      intro heta
      exact ht (by simp [heta])
    have hleftEq : Set.EqOn (fun t : ℝ => (eta0 t : ℂ) * E t)
        (fun t => L t * E t) (Set.uIcc (1 / 4 : ℝ) (1 / 2 : ℝ)) := by
      intro t ht
      norm_num [Set.uIcc] at ht
      change (eta0 t : ℂ) * E t = L t * E t
      rw [eta0_left_formula_fd ht.1 ht.2]
    have hrightEq : Set.EqOn (fun t : ℝ => (eta0 t : ℂ) * E t)
        (fun t => R t * E t) (Set.uIcc (1 / 2 : ℝ) 1) := by
      intro t ht
      norm_num [Set.uIcc] at ht
      change (eta0 t : ℂ) * E t = R t * E t
      rw [eta0_right_formula_fd ht.1 ht.2]
    have hiL : IntervalIntegrable (fun t : ℝ => (eta0 t : ℂ) * E t) volume
        (1 / 4 : ℝ) (1 / 2 : ℝ) := by
      rw [intervalIntegrable_congr (hleftEq.mono Set.uIoc_subset_uIcc)]
      exact (hLcont.mul hEcont.continuousOn).intervalIntegrable
    have hiR : IntervalIntegrable (fun t : ℝ => (eta0 t : ℂ) * E t) volume
        (1 / 2 : ℝ) 1 := by
      rw [intervalIntegrable_congr (hrightEq.mono Set.uIoc_subset_uIcc)]
      exact (hRcont.mul hEcont.continuousOn).intervalIntegrable
    calc
      (∫ t : ℝ, (eta0 t : ℂ) * E t) =
          ∫ t in (1 / 4 : ℝ)..1, (eta0 t : ℂ) * E t :=
        (intervalIntegral.integral_eq_integral_of_support_subset hsupp).symm
      _ = (∫ t in (1 / 4 : ℝ)..(1 / 2 : ℝ), (eta0 t : ℂ) * E t) +
          ∫ t in (1 / 2 : ℝ)..1, (eta0 t : ℂ) * E t := by
        rw [intervalIntegral.integral_add_adjacent_intervals hiL hiR]
      _ = (∫ t in (1 / 4 : ℝ)..(1 / 2 : ℝ), L t * E t) +
          ∫ t in (1 / 2 : ℝ)..1, R t * E t := by
        rw [intervalIntegral.integral_congr hleftEq,
          intervalIntegral.integral_congr hrightEq]
      _ = _ := by rw [hleftIBP, hrightIBP, hLzero, hRzero, hmid]; ring
  have hc_norm : ‖c‖ = 2 * Real.pi * |u| := by
    dsimp [c]
    simp [Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hE_norm (t : ℝ) : ‖E t‖ = 1 := by
    dsimp [E, c]
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I * (u : ℂ) * (t : ℂ) =
        ((2 * Real.pi * u * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hV_norm (t : ℝ) : ‖V t‖ = 1 / (2 * Real.pi * |u|) := by
    rw [show V t = E t / c by rfl, norm_div, hE_norm, hc_norm]
  have hdenpos : 0 < 2 * Real.pi * |u| :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (abs_pos.mpr hu)
  have hleftNorm :
      ‖∫ t in (1 / 4 : ℝ)..(1 / 2 : ℝ), dL t * V t‖ ≤
        4 * Real.log 2 / (2 * Real.pi * |u|) := by
    calc
      ‖∫ t in (1 / 4 : ℝ)..(1 / 2 : ℝ), dL t * V t‖
          ≤ ∫ t in (1 / 4 : ℝ)..(1 / 2 : ℝ),
              (4 / (2 * Real.pi * |u|)) * (1 / t) := by
            apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
            · filter_upwards with t ht
              norm_num [Set.mem_Ioc] at ht
              rw [norm_mul, hV_norm]
              dsimp [dL]
              rw [Complex.norm_real, Real.norm_eq_abs,
                abs_of_pos (div_pos (by norm_num) (by linarith : 0 < t))]
              exact le_of_eq (by ring)
            · apply ContinuousOn.intervalIntegrable
              intro t ht
              have ht0 : t ≠ 0 := by norm_num [Set.uIcc] at ht; linarith
              exact (continuousAt_const.mul
                (continuousAt_const.div continuousAt_id ht0)).continuousWithinAt
      _ = 4 * Real.log 2 / (2 * Real.pi * |u|) := by
        rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos
          (by norm_num) (by norm_num)]
        norm_num
        ring
  have hrightNorm :
      ‖∫ t in (1 / 2 : ℝ)..1, dR t * V t‖ ≤
        4 * Real.log 2 / (2 * Real.pi * |u|) := by
    calc
      ‖∫ t in (1 / 2 : ℝ)..1, dR t * V t‖
          ≤ ∫ t in (1 / 2 : ℝ)..1,
              (4 / (2 * Real.pi * |u|)) * (1 / t) := by
            apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
            · filter_upwards with t ht
              norm_num [Set.mem_Ioc] at ht
              rw [norm_mul, hV_norm]
              dsimp [dR]
              rw [Complex.norm_real, Real.norm_eq_abs,
                abs_of_neg (div_neg_of_neg_of_pos (by norm_num) (by linarith : 0 < t))]
              exact le_of_eq (by ring)
            · apply ContinuousOn.intervalIntegrable
              intro t ht
              have ht0 : t ≠ 0 := by norm_num [Set.uIcc] at ht; linarith
              exact (continuousAt_const.mul
                (continuousAt_const.div continuousAt_id ht0)).continuousWithinAt
      _ = 4 * Real.log 2 / (2 * Real.pi * |u|) := by
        rw [intervalIntegral.integral_const_mul, integral_one_div_of_pos
          (by norm_num) (by norm_num)]
        norm_num
        ring
  have htarget :
      (∫ t : ℝ, (eta0 t : ℂ) * expCircle (u * t)) =
        ∫ t : ℝ, (eta0 t : ℂ) * E t := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [hE_exp]
  rw [htarget]
  rw [hpiece]
  calc
    ‖-(∫ t in (1 / 4 : ℝ)..(1 / 2 : ℝ), dL t * V t) -
        (∫ t in (1 / 2 : ℝ)..1, dR t * V t)‖
        ≤ ‖-(∫ t in (1 / 4 : ℝ)..(1 / 2 : ℝ), dL t * V t)‖ +
          ‖∫ t in (1 / 2 : ℝ)..1, dR t * V t‖ := by
            exact norm_sub_le _ _
    _ = ‖∫ t in (1 / 4 : ℝ)..(1 / 2 : ℝ), dL t * V t‖ +
          ‖∫ t in (1 / 2 : ℝ)..1, dR t * V t‖ := by rw [norm_neg]
    _ ≤ 4 * Real.log 2 / (2 * Real.pi * |u|) +
        4 * Real.log 2 / (2 * Real.pi * |u|) := add_le_add hleftNorm hrightNorm
    _ = 8 * Real.log 2 / (2 * Real.pi * |u|) := by ring

end TaoFivePrimes

open TaoFivePrimes

theorem solution (u : ℝ) (hu : u ≠ 0) :
    norm (∫ t : ℝ, (eta0 t : ℂ) * expCircle (u * t)) ≤
      8 * Real.log 2 / (2 * Real.pi * |u|) := by
  exact TaoFivePrimes.eta0_fourier_decay_variation_source_proof u hu

#print axioms solution
