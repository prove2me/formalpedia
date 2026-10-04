-- Prove2me | solution 1 for PiIrrationality.chudnovsky_rate_certificate
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-03T16:55:16.175091+00:00
-- url     : https://prove2.me/submissions/6eced779-b7cb-416a-83e1-50a6ec419182

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

set_option autoImplicit false

lemma chudnovsky_cos_bounds :
    (9659258262890 / 10000000000000 : ℝ) < Real.cos (Real.pi / 12) ∧
    Real.cos (Real.pi / 12) < (9659258262891 / 10000000000000 : ℝ) := by
  have hs2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hs3 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hb2 : (1414213562373095 / 1000000000000000 : ℝ) < Real.sqrt 2 ∧
      Real.sqrt 2 < (1414213562373096 / 1000000000000000 : ℝ) := by
    constructor <;> nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hb3 : (1732050807568877 / 1000000000000000 : ℝ) < Real.sqrt 3 ∧
      Real.sqrt 3 < (1732050807568878 / 1000000000000000 : ℝ) := by
    constructor <;> nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hc : Real.cos (Real.pi / 12) =
      Real.sqrt 2 / 2 * (Real.sqrt 3 / 2) + Real.sqrt 2 / 2 * (1 / 2) := by
    have heq : Real.pi / 12 = Real.pi / 4 - Real.pi / 6 := by ring
    rw [heq, Real.cos_sub, Real.cos_pi_div_four, Real.cos_pi_div_six,
      Real.sin_pi_div_four, Real.sin_pi_div_six]
  rw [hc]
  constructor
  · nlinarith [mul_pos (sub_pos.mpr hb2.1) (sub_pos.mpr hb3.1)]
  · nlinarith [mul_pos (sub_pos.mpr hb2.2) (sub_pos.mpr hb3.2)]

lemma chudnovsky_log_sin_bound :
    Real.log (2 * Real.sin (Real.pi / 24)) < (-1.3430341845 : ℝ) := by
  have hspos : 0 < Real.sin (Real.pi / 24) := by
    apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]
  have htrig := Real.sin_sq_add_cos_sq (Real.pi / 24)
  have hdbl := Real.cos_two_mul (Real.pi / 24)
  have heq : 2 * (Real.pi / 24) = Real.pi / 12 := by ring
  rw [heq] at hdbl
  have hsq : (2 * Real.sin (Real.pi / 24))^2 < (68148347422 / 1000000000000 : ℝ) := by
    nlinarith [chudnovsky_cos_bounds.1]
  have hlog := Real.log_lt_log (by positivity : 0 < (2 * Real.sin (Real.pi / 24))^2) hsq
  rw [Real.log_pow] at hlog
  have hz := Real.abs_log_sub_add_sum_range_le
    (x := -(90373558752 / 1000000000000 : ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ] at hz
  have hupper := (abs_le.mp hz).2
  have hid : Real.log (1090373558752 / 1000000000000 : ℝ) =
      Real.log (68148347422 / 1000000000000 : ℝ) + 4 * Real.log 2 := by
    have hp := Real.log_pow 2 4
    norm_num at hp
    rw [← hp, ← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  norm_num at hid hlog
  rw [hid] at hupper
  linarith [Real.log_two_gt_d9]

lemma chudnovsky_log_cos_bound :
    Real.log (2 * Real.cos (Real.pi / 24)) < (0.6845552370 : ℝ) := by
  have hcpos : 0 < Real.cos (Real.pi / 24) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have hdbl := Real.cos_two_mul (Real.pi / 24)
  have heq : 2 * (Real.pi / 24) = Real.pi / 12 := by ring
  rw [heq] at hdbl
  have hsq : (2 * Real.cos (Real.pi / 24))^2 < (39318516525782 / 10000000000000 : ℝ) := by
    nlinarith [chudnovsky_cos_bounds.2]
  have hlog := Real.log_lt_log (by positivity : 0 < (2 * Real.cos (Real.pi / 24))^2) hsq
  rw [Real.log_pow] at hlog
  have hz := Real.abs_log_sub_add_sum_range_le
    (x := (1703708685545 / 100000000000000 : ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at hz
  have hupper := (abs_le.mp hz).2
  have hid : Real.log (98296291314455 / 100000000000000 : ℝ) =
      Real.log (39318516525782 / 10000000000000 : ℝ) - 2 * Real.log 2 := by
    have hp := Real.log_pow 2 2
    norm_num at hp
    rw [← hp, ← Real.log_div (by norm_num) (by norm_num)]
    norm_num
  norm_num at hid hlog
  rw [hid] at hupper
  linarith [Real.log_two_lt_d9]

theorem solution :
    0 < -6 * Real.log (2 * Real.sin (Real.pi / 24)) - 5 ∧
    5 * (1 + (5 + 6 * Real.log (2 * Real.cos (Real.pi / 24))) /
      (-6 * Real.log (2 * Real.sin (Real.pi / 24)) - 5)) < (19.8899945 : ℝ) := by
  have hs := chudnovsky_log_sin_bound
  have hc := chudnovsky_log_cos_bound
  have hd : 0 < -6 * Real.log (2 * Real.sin (Real.pi / 24)) - 5 := by linarith
  refine ⟨hd, ?_⟩
  have hquot : (5 + 6 * Real.log (2 * Real.cos (Real.pi / 24))) /
      (-6 * Real.log (2 * Real.sin (Real.pi / 24)) - 5) < (19.8899945 : ℝ) / 5 - 1 := by
    apply (div_lt_iff₀ hd).2
    linarith
  linarith
