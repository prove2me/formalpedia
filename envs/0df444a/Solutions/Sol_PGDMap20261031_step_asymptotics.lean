-- Prove2me | solution 1 for PGDMap20261031.step_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-31T16:01:03.949248+00:00
-- url     : https://prove2.me/submissions/2d8511ab-b92d-4bc6-98d5-ec3796103680

import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Theorems.Thm_PGDMap20261031_step_balance
import Theorems.Thm_PGDMap20261031_step_scalar_equations
import Theorems.Thm_PGDMap20261031_step_monotonicity

open PGDMap20261031 Filter Topology
noncomputable section

private abbrev count (n : ℕ) : ℕ := 2 * (n + 1)
private abbrev H (q : ℝ) (n : ℕ) : ℝ := optimalStep (n + 2) q
private abbrev T (q : ℝ) (n : ℕ) : ℝ := H q n - 1

private lemma count_cast (n : ℕ) : (count n : ℝ) = 2 * ((n + 1 : ℕ) : ℝ) := by push_cast; rfl

private lemma count_tendsto : Tendsto count atTop atTop := by
  apply tendsto_atTop.2
  intro b
  exact eventually_atTop.2 ⟨b, fun n hn => by dsimp [count]; omega⟩

private lemma H_bounds (q : ℝ) (hq : 0 ≤ q) (n : ℕ) : 1 < H q n ∧ H q n < 2 := by
  have h := PGDMap20261031.step_balance (n + 2) q (by omega) hq
  exact ⟨h.1, h.2.1⟩

private lemma T_bounds (q : ℝ) (hq : 0 ≤ q) (n : ℕ) : 0 < T q n ∧ T q n < 1 := by
  have h := H_bounds q hq n
  dsimp [T]
  constructor <;> linarith

private lemma zero_root (n : ℕ) : (T 0 n) ^ count n * (1 + (count n : ℝ) * H 0 n) = 1 := by
  have hb := H_bounds 0 (by norm_num) n
  have h := (PGDMap20261031.step_scalar_equations (n + 2) 0 (H 0 n)
    (by omega) (by norm_num) hb.1 hb.2).mp rfl
  simpa only [if_pos rfl, ite_true, show n + 2 - 1 = n + 1 by omega, count_cast] using h

private lemma H_zero_limit : Tendsto (H 0) atTop (𝓝 2) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    by_cases ha1 : a ≤ 1
    · exact Eventually.of_forall (fun n => lt_of_le_of_lt ha1 (H_bounds 0 (by norm_num) n).1)
    · have harp : 0 < a - 1 := by linarith
      have har1 : a - 1 < 1 := by linarith
      have hp := tendsto_pow_atTop_nhds_zero_of_lt_one harp.le har1
      have hm := tendsto_self_mul_const_pow_of_lt_one harp.le har1
      have hgeom : Tendsto (fun m : ℕ => (a - 1) ^ m * (1 + 2 * (m : ℝ))) atTop (𝓝 0) := by
        convert hp.add (hm.const_mul 2) using 1 <;> first | rfl | simp | (funext m; ring)
      have hsmall : ∀ᶠ n : ℕ in atTop,
          (a - 1) ^ count n * (1 + 2 * (count n : ℝ)) < 1 :=
        (tendsto_order.1 (hgeom.comp count_tendsto)).2 1 (by norm_num)
      filter_upwards [hsmall] with n hsmall
      by_contra hn
      have hle : H 0 n ≤ a := le_of_not_gt hn
      have hT := T_bounds 0 (by norm_num) n
      have hpow : (T 0 n) ^ count n ≤ (a - 1) ^ count n :=
        pow_le_pow_left₀ hT.1.le (by dsimp [T]; linarith) _
      have hcoef : 1 + (count n : ℝ) * H 0 n ≤ 1 + 2 * (count n : ℝ) := by
        have hc : (0 : ℝ) ≤ count n := Nat.cast_nonneg _
        nlinarith [(H_bounds 0 (by norm_num) n).2]
      have hprod := mul_le_mul hpow hcoef
        (add_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (by linarith [(H_bounds 0 (by norm_num) n).1])))
        (pow_nonneg harp.le _)
      rw [zero_root] at hprod
      linarith only [hsmall, hprod]
  · intro b hb
    exact Eventually.of_forall (fun n => lt_trans (H_bounds 0 (by norm_num) n).2 hb)

private lemma H_limit (q : ℝ) (hq : 0 ≤ q) : Tendsto (H q) atTop (𝓝 2) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have hev := (tendsto_order.1 H_zero_limit).1 a ha
    filter_upwards [hev] with n hn
    by_cases hz : q = 0
    · simpa only [hz] using hn
    · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hz)
      exact lt_trans hn (PGDMap20261031.step_monotonicity.1 (n + 2) 0 q (by omega) (by norm_num) hqp)
  · intro b hb
    exact Eventually.of_forall (fun n => lt_trans (H_bounds q hq n).2 hb)

private abbrev Z (q : ℝ) (n : ℕ) : ℝ := ((base (H q n) q) ^ count n)⁻¹

private lemma positive_root (q : ℝ) (hq : 0 < q) (n : ℕ) :
    (T q n) ^ count n = q / (1 + q - Z q n) := by
  have hb := H_bounds q hq.le n
  have h := (PGDMap20261031.step_scalar_equations (n + 2) q (H q n)
    (by omega) hq.le hb.1 hb.2).mp rfl
  rw [if_neg hq.ne'] at h
  simp only [show n + 2 - 1 = n + 1 by omega] at h
  have hzpow : (base (H q n) q) ^ (-(2 * ((n + 1 : ℕ) : ℤ))) = Z q n := by
    rw [show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) = ((count n : ℕ) : ℤ) by push_cast; rfl,
      zpow_neg, zpow_natCast]
  simpa only [hzpow] using h

private lemma Z_limit (q : ℝ) (hq : 0 < q) : Tendsto (Z q) atTop (𝓝 0) := by
  have hb : 0 < 1 + q := by linarith
  have hrpos : 0 < (1 + q)⁻¹ := inv_pos.mpr hb
  have hrlt : (1 + q)⁻¹ < 1 := by
    rw [← one_div]
    apply (div_lt_one hb).2
    linarith
  have hupper : Tendsto (fun n => ((1 + q)⁻¹) ^ count n) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hrpos.le hrlt).comp count_tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
  · intro n
    exact inv_nonneg.mpr (pow_nonneg (by unfold base; nlinarith [(H_bounds q hq.le n).1]) _)
  · intro n
    have hbq : 1 + q ≤ base (H q n) q := by unfold base; nlinarith [(H_bounds q hq.le n).1]
    have hp := pow_le_pow_left₀ hb.le hbq (count n)
    change ((base (H q n) q) ^ count n)⁻¹ ≤ ((1 + q)⁻¹) ^ count n
    rw [inv_pow]
    exact (inv_le_inv₀ (pow_pos (lt_of_lt_of_le hb hbq) _) (pow_pos hb _)).mpr hp

private lemma T_limit (q : ℝ) (hq : 0 ≤ q) : Tendsto (T q) atTop (𝓝 1) := by
  convert (H_limit q hq).sub_const 1 using 1 <;> first | rfl | norm_num

private lemma logarithmic_ratio_limit (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun n => (T q n - 1) / Real.log (T q n)) atTop (𝓝 1) := by
  have ht : Tendsto (T q) atTop (𝓝[≠] (1 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨T_limit q hq, Eventually.of_forall ?_⟩
    intro n
    exact (T_bounds q hq n).2.ne
  have hlog := (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope.comp ht
  have hquot : Tendsto (fun n => Real.log (T q n) / (T q n - 1)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, slope_def_field, Real.log_one, sub_zero, inv_one] using hlog
  convert hquot.inv₀ (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> first | rfl | simp

private lemma positive_asymptotic (q : ℝ) (hq : 0 < q) :
    Tendsto (fun n => (count n : ℝ) * (2 - H q n)) atTop (𝓝 (Real.log (1 + 1 / q))) := by
  have hz := Z_limit q hq
  have hdenlim : Tendsto (fun n => 1 + q - Z q n) atTop (𝓝 (1 + q)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hz
  have hrlim : Tendsto (fun n => q / (1 + q - Z q n)) atTop (𝓝 (q / (1 + q))) :=
    tendsto_const_nhds.div hdenlim (by linarith)
  have hneglog : Tendsto (fun n => -((count n : ℝ) * Real.log (T q n)))
      atTop (𝓝 (-Real.log (q / (1 + q)))) := by
    convert (hrlim.log (div_pos hq (by linarith)).ne').neg using 1
    funext n
    rw [← positive_root q hq n, Real.log_pow]
  have hlogeq : -Real.log (q / (1 + q)) = Real.log (1 + 1 / q) := by
    rw [← Real.log_inv]
    congr 1
    field_simp [hq.ne']
    ring
  rw [hlogeq] at hneglog
  convert hneglog.mul (logarithmic_ratio_limit q hq.le) using 1
  · funext n
    have hlogne : Real.log (T q n) ≠ 0 := (Real.log_neg (T_bounds q hq.le n).1 (T_bounds q hq.le n).2).ne
    change (count n : ℝ) * (2 - H q n) = _
    field_simp [hlogne]
    try dsimp [T]
    ring
  · simp

private lemma count_real_limit : Tendsto (fun n : ℕ => (count n : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp count_tendsto

private lemma count_real_pos (n : ℕ) : (0 : ℝ) < count n := by
  exact_mod_cast (show 0 < count n by dsimp [count]; omega)

private lemma zero_log_root (n : ℕ) :
    -((count n : ℝ) * Real.log (T 0 n)) = Real.log (1 + (count n : ℝ) * H 0 n) := by
  have ht := T_bounds 0 (by norm_num) n
  have hcoef : 0 < 1 + (count n : ℝ) * H 0 n := by
    have := H_bounds 0 (by norm_num) n
    nlinarith [count_real_pos n, mul_pos (count_real_pos n) (by linarith : 0 < H 0 n)]
  have h := congrArg Real.log (zero_root n)
  rw [Real.log_mul (pow_pos ht.1 _).ne' hcoef.ne', Real.log_pow, Real.log_one] at h
  linarith only [h]

private lemma zero_delta_bound (n : ℕ) :
    (count n : ℝ) * (2 - H 0 n) ≤ Real.log (1 + 2 * (count n : ℝ)) := by
  have ht := T_bounds 0 (by norm_num) n
  have hh := H_bounds 0 (by norm_num) n
  have hm := count_real_pos n
  have hlog := Real.log_le_sub_one_of_pos ht.1
  have hlogscaled := mul_le_mul_of_nonneg_left hlog hm.le
  have hcoef : 0 < 1 + (count n : ℝ) * H 0 n := by nlinarith [mul_pos hm (by linarith : 0 < H 0 n)]
  have hu := Real.log_le_log hcoef (show 1 + (count n : ℝ) * H 0 n ≤ 1 + 2 * (count n : ℝ) by
    nlinarith)
  rw [← zero_log_root] at hu
  dsimp only [T] at hlogscaled
  linarith only [hlogscaled, hu]

private lemma zero_delta_square_limit :
    Tendsto (fun n => (count n : ℝ) * (2 - H 0 n) ^ 2) atTop (𝓝 0) := by
  have hx : Tendsto (fun n => 1 + 2 * (count n : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_atTop.1 count_real_limit) ((b - 1) / 2)] with n hn
    linarith
  have hloglim : Tendsto (fun n => Real.log (1 + 2 * (count n : ℝ)) ^ 2 / (count n : ℝ))
      atTop (𝓝 0) := by
    convert (Real.tendsto_pow_log_div_mul_add_atTop (1 / 2) (-1 / 2) 2 (by norm_num)).comp hx using 1
    funext n
    congr 1
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hloglim
  · intro n
    exact mul_nonneg (count_real_pos n).le (sq_nonneg _)
  · intro n
    have hm := count_real_pos n
    have hh := H_bounds 0 (by norm_num) n
    have hbound := zero_delta_bound n
    have hleft : 0 ≤ (count n : ℝ) * (2 - H 0 n) := mul_nonneg hm.le (by linarith)
    have hsq := pow_le_pow_left₀ hleft hbound 2
    apply (le_div_iff₀ hm).2
    nlinarith only [hsq]

private lemma log_remainder (t : ℝ) (ht : 0 < t) (_ht1 : t < 1) :
    0 ≤ -Real.log t - (1 - t) ∧
    -Real.log t - (1 - t) ≤ (1 - t) ^ 2 / t := by
  have hlo := Real.log_le_sub_one_of_pos ht
  have hhi := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at hhi
  have hhimul := mul_le_mul_of_nonneg_right hhi ht.le
  have hid : (t⁻¹ - 1) * t = 1 - t := by rw [sub_mul, inv_mul_cancel₀ ht.ne', one_mul]
  rw [hid] at hhimul
  constructor
  · linarith only [hlo]
  · apply (le_div_iff₀ ht).2
    nlinarith only [hhimul]

private lemma zero_log_error_limit :
    Tendsto (fun n => (count n : ℝ) * (2 - H 0 n) -
      Real.log (1 + (count n : ℝ) * H 0 n)) atTop (𝓝 0) := by
  have hupper : Tendsto (fun n => (count n : ℝ) * (2 - H 0 n) ^ 2 / T 0 n)
      atTop (𝓝 0) := by
    convert zero_delta_square_limit.div (T_limit 0 (by norm_num)) (by norm_num : (1 : ℝ) ≠ 0)
      using 1 <;> first | rfl | simp
  have herr : Tendsto (fun n => (count n : ℝ) * (-Real.log (T 0 n) - (1 - T 0 n)))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    · intro n
      have hr := log_remainder (T 0 n) (T_bounds 0 (by norm_num) n).1 (T_bounds 0 (by norm_num) n).2
      exact mul_nonneg (count_real_pos n).le hr.1
    · intro n
      have hr := log_remainder (T 0 n) (T_bounds 0 (by norm_num) n).1 (T_bounds 0 (by norm_num) n).2
      have hm := mul_le_mul_of_nonneg_left hr.2 (count_real_pos n).le
      convert hm using 1
      dsimp only [T]
      ring
  convert herr.neg using 1
  · funext n
    rw [← zero_log_root]
    dsimp only [T]
    ring
  · simp

private lemma zero_log_ratio_limit :
    Tendsto (fun n => Real.log (1 + (count n : ℝ) * H 0 n) -
      Real.log (2 * (count n : ℝ))) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => (1 / 2 : ℝ) / (count n : ℝ)) atTop (𝓝 0) :=
    count_real_limit.const_div_atTop (1 / 2)
  have hratio : Tendsto (fun n => (1 + (count n : ℝ) * H 0 n) / (2 * (count n : ℝ)))
      atTop (𝓝 1) := by
    convert (H_zero_limit.div_const 2).add hinv using 1
    · funext n
      field_simp [(count_real_pos n).ne']
      ring
    · norm_num
  have hlog := hratio.log (by norm_num : (1 : ℝ) ≠ 0)
  convert hlog using 1
  · funext n
    have hh := H_bounds 0 (by norm_num) n
    have hcoef : 0 < 1 + (count n : ℝ) * H 0 n := by
      nlinarith [mul_pos (count_real_pos n) (by linarith : 0 < H 0 n)]
    rw [Real.log_div hcoef.ne' (mul_pos (by norm_num : (0 : ℝ) < 2) (count_real_pos n)).ne']
  · simp

private lemma zero_asymptotic :
    Tendsto (fun n => (count n : ℝ) * (2 - H 0 n) - Real.log (2 * (count n : ℝ)))
      atTop (𝓝 0) := by
  convert zero_log_error_limit.add zero_log_ratio_limit using 1 <;>
    first | simp | (funext n; ring)

theorem solution : StepAsymptoticsClaim := by
  refine ⟨H_limit, ?_, ?_⟩
  · intro q hq
    simpa only [count_cast] using positive_asymptotic q hq
  · convert zero_asymptotic using 1
    funext n
    rw [count_cast]
    congr 2
    ring
