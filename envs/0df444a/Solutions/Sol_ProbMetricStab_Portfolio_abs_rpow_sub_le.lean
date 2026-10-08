-- Prove2me | solution 1 for ProbMetricStab.Portfolio.abs_rpow_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T08:05:14.111676+00:00
-- url     : https://prove2.me/submissions/769103b2-87dd-42c6-846b-a972c34cae26

import Mathlib
import Definitions.Def_ProbMetricStab_Portfolio_Setting

private lemma log_bound {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    |Real.log u| * u ≤ Real.exp (-1) := by
  have hl : Real.log u ≤ 0 := Real.log_nonpos hu.le hu1
  rw [abs_of_nonpos hl]
  have h := Real.add_one_le_exp (-Real.log u - 1)
  have he : Real.exp (-Real.log u - 1) * u = Real.exp (-1) := by
    rw [Real.exp_sub, Real.exp_neg, Real.exp_log hu]
    rw [Real.exp_neg]
    field_simp
  have hh := mul_le_mul_of_nonneg_right h hu.le
  rw [he] at hh
  nlinarith

theorem solution (α α' : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (hα'1 : 1 < α') (hα'2 : α' < 2)
    (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |(|t| ^ α - |t| ^ α')| ≤ Real.exp (-1) * |α - α'| := by
  have ht1 : |t| ≤ 1 := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
  by_cases hz : |t| = 0
  · simp [hz, Real.zero_rpow (by linarith : α ≠ 0), Real.zero_rpow (by linarith : α' ≠ 0)]
    positivity
  have hp : 0 < |t| := lt_of_le_of_ne (abs_nonneg t) (Ne.symm hz)
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun z : ℝ => |t| ^ z) (C := Real.exp (-1))
    (fun z _ => ((hasDerivAt_id z).const_rpow hp).differentiableAt)
    (fun z hz => ?_) (convex_Ici (1 : ℝ)) hα'1.le hα1.le
  · simpa only [Real.norm_eq_abs] using hh
  · rw [deriv_const_rpow_id hp, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
    calc
      abs (Real.log (abs t)) * |t| ^ z ≤ abs (Real.log (abs t)) * |t| :=
        mul_le_mul_of_nonneg_left (by
          simpa using Real.rpow_le_rpow_of_exponent_ge hp ht1 hz) (abs_nonneg _)
      _ ≤ _ := log_bound hp ht1

#print axioms solution
