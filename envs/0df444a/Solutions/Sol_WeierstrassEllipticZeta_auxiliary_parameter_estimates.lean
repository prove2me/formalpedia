-- Prove2me | solution 1 for WeierstrassEllipticZeta.auxiliary_parameter_estimates
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-07T15:04:16.148595+00:00
-- url     : https://prove2.me/submissions/d2fb368d-d821-400d-b364-e6e075395292

import Definitions.Def_WeierstrassEllipticZeta_AuxiliaryParameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 600000

open Filter
open scoped Topology

open WeierstrassEllipticZeta

private lemma floor_half_le {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℝ) := by
  have := Nat.lt_floor_add_one x
  linarith

private lemma tendsto_div_log :
    Tendsto (fun x : ℝ ↦ x / Real.log x) atTop atTop := by
  have h := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hp : ∀ᶠ x : ℝ in atTop, 0 < Real.log x / x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (Real.log_pos hx) (by linarith)
  simpa only [Function.comp_def, inv_div, id_eq] using
    (tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨h, hp⟩))

private lemma real_parameter_counts (x : ℝ) (hx : 1 < x)
    (ha : 1 ≤ x / Real.log x)
    (hs : 2 ≤ x ^ (3 / 16 : ℝ))
    (hq : 2 ≤ x ^ (5 / 8 : ℝ) * Real.log x / 64) :
    let m := ⌊x / Real.log x⌋₊
    let l := ⌊Real.sqrt (x * Real.log x)⌋₊
    let s := ⌊x ^ (3 / 16 : ℝ)⌋₊
    let q := ⌊x ^ (5 / 8 : ℝ) * Real.log x / 64⌋₊
    x ^ 2 / 512 ≤ (m + 1 : ℝ) * s ^ 2 * q ∧
    (m + 1 : ℝ) * s ^ 2 * q ≤ x ^ 2 / 32 ∧
    x ^ 2 ≤ (m + 1 : ℝ) * (l + 1 : ℝ) ^ 2 := by
  dsimp only
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hp : (x ^ (3 / 16 : ℝ)) ^ 2 * x ^ (5 / 8 : ℝ) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    norm_num
  have hsq : (Real.sqrt (x * Real.log x)) ^ 2 = x * Real.log x :=
    Real.sq_sqrt (by positivity)
  have hmul : x / Real.log x * (Real.sqrt (x * Real.log x)) ^ 2 = x ^ 2 := by
    rw [hsq]
    field_simp
  have hmlo := (Nat.lt_floor_add_one (x / Real.log x)).le
  have hmhi : (⌊x / Real.log x⌋₊ : ℝ) + 1 ≤ 2 * (x / Real.log x) := by
    have := Nat.floor_le (by positivity : 0 ≤ x / Real.log x)
    linarith
  have hslo := floor_half_le hs
  have hshi := Nat.floor_le (by positivity : 0 ≤ x ^ (3 / 16 : ℝ))
  have hqlo := floor_half_le hq
  have hqhi := Nat.floor_le (by positivity : 0 ≤ x ^ (5 / 8 : ℝ) * Real.log x / 64)
  have hlo := (Nat.lt_floor_add_one (Real.sqrt (x * Real.log x))).le
  have he : x / Real.log x * (x ^ (3 / 16 : ℝ)) ^ 2 *
      (x ^ (5 / 8 : ℝ) * Real.log x / 64) = x ^ 2 / 64 := by
    calc
      _ = x / Real.log x *
          ((x ^ (3 / 16 : ℝ)) ^ 2 * x ^ (5 / 8 : ℝ)) * Real.log x / 64 := by ring
      _ = x ^ 2 / 64 := by rw [hp]; field_simp
  constructor
  · have h := mul_le_mul
      (mul_le_mul hmlo (pow_le_pow_left₀ (by positivity) hslo 2)
        (by positivity) (by positivity)) hqlo (by positivity) (by positivity)
    nlinarith only [h, he]
  constructor
  · have h := mul_le_mul
      (mul_le_mul hmhi (pow_le_pow_left₀ (by positivity) hshi 2)
        (by positivity) (by positivity)) hqhi (by positivity) (by positivity)
    nlinarith only [h, he]
  · have h := mul_le_mul hmlo (pow_le_pow_left₀ (by positivity) hlo 2)
      (by positivity) (by positivity)
    nlinarith only [h, hmul]

private lemma log_power_bound (r s ε : ℝ) (hs : 0 < s) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, (Real.log x) ^ r ≤ ε * x ^ s := by
  have h := (isLittleO_log_rpow_rpow_atTop r hs).bound hε
  filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg
    (Real.log_nonneg hx1) r), abs_of_nonneg (Real.rpow_nonneg (by linarith) s)] using hx

theorem solution (A : ℝ) (hA : 0 < A) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ auxiliaryL0 N ∧ 1 ≤ auxiliaryL N ∧ 2 ≤ auxiliaryS N ∧
      1 ≤ auxiliaryS3 N ∧ auxiliaryS N ≤ auxiliaryS3 N ∧
      8 * ((auxiliaryL0 N + 1) * auxiliaryS N ^ 2 * auxiliaryS3 N) ≤
        (auxiliaryL0 N + 1) * (auxiliaryL N + 1) ^ 2 ∧
      (N : ℝ) ^ 2 / 512 ≤
        (auxiliaryL0 N + 1 : ℝ) * auxiliaryS N ^ 2 * auxiliaryS3 N ∧
      (auxiliaryL0 N + 1 : ℝ) * auxiliaryS N ^ 2 * auxiliaryS3 N ≤
        (N : ℝ) ^ 2 / 32 ∧
      (auxiliaryL0 N : ℝ) * Real.log N ≤ N ∧
      auxiliaryL N * auxiliaryS N ^ 2 ≤ auxiliaryL0 N ∧
      1 ≤ auxiliaryRadius N ∧
      8 * A * auxiliaryS3 N / auxiliaryRadius N ≤ (N : ℝ) ^ (-1 / 36 : ℝ) ∧
      A * auxiliaryL N * auxiliaryRadius N ^ 2 ≤ (N : ℝ) ^ 2 := by
  have hm := tendsto_div_log.eventually_ge_atTop 2
  have hs := (tendsto_rpow_atTop (by norm_num : 0 < (3 / 16 : ℝ))).eventually_ge_atTop 2
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop 64
  have hb := log_power_bound (3 / 2) (1 / 8) (1 / 2) (by norm_num) (by norm_num)
  have hr := log_power_bound 1 (1 / 36) (8 / A) (by norm_num) (by positivity)
  have hg := log_power_bound (1 / 2) (5 / 36) (1 / A) (by norm_num) (by positivity)
  unfold auxiliaryL0 auxiliaryL auxiliaryS auxiliaryS3 auxiliaryRadius
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [hn.eventually hm, hn.eventually hs, hn.eventually hlog,
    hn.eventually hb, hn.eventually hr, hn.eventually hg,
    hn.eventually (eventually_ge_atTop (2 : ℝ))]
    with N hm hs hlog hb hr hg hx
  let x : ℝ := N
  have hx0 : 0 < x := by linarith only [hx]
  have hlog0 : 0 < Real.log x := by linarith only [hlog]
  have hxp : (1 : ℝ) ≤ x := by linarith only [hx]
  have hq : 2 ≤ x ^ (5 / 8 : ℝ) * Real.log x / 64 := by
    have hpow := Real.rpow_le_rpow_of_exponent_le hxp
      (by norm_num : (3 / 16 : ℝ) ≤ 5 / 8)
    nlinarith only [hs, hpow, mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ x ^ (5 / 8 : ℝ))]
  have hsq : 1 ≤ Real.sqrt (x * Real.log x) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith only [hx, hlog]
  have hc := real_parameter_counts x (by linarith) (by linarith) hs hq
  dsimp only at hc
  have hmnat : 1 ≤ ⌊x / Real.log x⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hlnat : 1 ≤ ⌊Real.sqrt (x * Real.log x)⌋₊ := (Nat.one_le_floor_iff _).mpr hsq
  have hsnat : 2 ≤ ⌊x ^ (3 / 16 : ℝ)⌋₊ := (Nat.le_floor_iff (by positivity)).mpr hs
  have hqnat : 1 ≤ ⌊x ^ (5 / 8 : ℝ) * Real.log x / 64⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (by linarith)
  have hsnq : ⌊x ^ (3 / 16 : ℝ)⌋₊ ≤ ⌊x ^ (5 / 8 : ℝ) * Real.log x / 64⌋₊ := by
    apply Nat.floor_mono
    have hpow := Real.rpow_le_rpow_of_exponent_le hxp
      (by norm_num : (3 / 16 : ℝ) ≤ 5 / 8)
    nlinarith only [hs, hpow, mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ x ^ (5 / 8 : ℝ))]
  have hgap : 8 * ((⌊x / Real.log x⌋₊ + 1) * ⌊x ^ (3 / 16 : ℝ)⌋₊ ^ 2 *
      ⌊x ^ (5 / 8 : ℝ) * Real.log x / 64⌋₊) ≤
      (⌊x / Real.log x⌋₊ + 1) * (⌊Real.sqrt (x * Real.log x)⌋₊ + 1) ^ 2 := by
    have h : (8 : ℝ) * (((⌊x / Real.log x⌋₊ : ℝ) + 1) *
        (⌊x ^ (3 / 16 : ℝ)⌋₊ : ℝ) ^ 2 * ⌊x ^ (5 / 8 : ℝ) * Real.log x / 64⌋₊) ≤
        ((⌊x / Real.log x⌋₊ : ℝ) + 1) * ((⌊Real.sqrt (x * Real.log x)⌋₊ : ℝ) + 1) ^ 2 := by
      nlinarith only [hc.2.1, hc.2.2, sq_nonneg x]
    exact_mod_cast h
  have hmlog : (⌊x / Real.log x⌋₊ : ℝ) * Real.log x ≤ x := by
    exact (le_div_iff₀ hlog0).mp (Nat.floor_le (by positivity))
  have hls : ⌊Real.sqrt (x * Real.log x)⌋₊ * ⌊x ^ (3 / 16 : ℝ)⌋₊ ^ 2 ≤
      ⌊x / Real.log x⌋₊ := by
    have he : Real.sqrt (x * Real.log x) * (x ^ (3 / 16 : ℝ)) ^ 2 * Real.log x =
        x ^ (7 / 8 : ℝ) * (Real.log x) ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul_natCast hx0.le]
      calc
        _ = (x ^ (1 / 2 : ℝ) * x ^ ((3 / 16 : ℝ) * 2)) *
            ((Real.log x) ^ (1 / 2 : ℝ) * Real.log x) := by ring
        _ = _ := by rw [← Real.rpow_add hx0, ← Real.rpow_add_one hlog0.ne']; norm_num
    have hbound := mul_le_mul_of_nonneg_left hb (by positivity : 0 ≤ x ^ (7 / 8 : ℝ))
    have hprod : x ^ (7 / 8 : ℝ) * x ^ (1 / 8 : ℝ) = x := by
      rw [← Real.rpow_add hx0]; norm_num
    have hupper : Real.sqrt (x * Real.log x) * (x ^ (3 / 16 : ℝ)) ^ 2 ≤
        (x / Real.log x) / 2 := by
      apply (mul_le_mul_iff_of_pos_right hlog0).mp
      rw [he]
      have he' : x / Real.log x / 2 * Real.log x = x / 2 := by field_simp
      rw [he']
      nlinarith only [hbound, hprod]
    have hfloor := mul_le_mul (Nat.floor_le (Real.sqrt_nonneg (x * Real.log x)))
      (pow_le_pow_left₀ (by positivity) (Nat.floor_le (by positivity : 0 ≤ x ^ (3 / 16 : ℝ))) 2)
      (by positivity) (by positivity)
    have hhalf := floor_half_le hm
    have hfinal := hfloor.trans (hupper.trans hhalf)
    exact_mod_cast hfinal
  have hR : 1 ≤ x ^ (49 / 72 : ℝ) := Real.one_le_rpow hxp (by norm_num)
  have hrad : 8 * A * (⌊x ^ (5 / 8 : ℝ) * Real.log x / 64⌋₊ : ℝ) /
      x ^ (49 / 72 : ℝ) ≤ x ^ (-1 / 36 : ℝ) := by
    have hf := Nat.floor_le (by positivity : 0 ≤ x ^ (5 / 8 : ℝ) * Real.log x / 64)
    have hpow : x ^ (-1 / 36 : ℝ) * x ^ (49 / 72 : ℝ) =
        x ^ (5 / 8 : ℝ) * x ^ (1 / 36 : ℝ) := by
      rw [← Real.rpow_add hx0, ← Real.rpow_add hx0]; norm_num
    apply (div_le_iff₀ (by positivity)).mpr
    rw [hpow]
    simp only [Real.rpow_one] at hr
    have h := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ A * x ^ (5 / 8 : ℝ))
    have he : A * x ^ (5 / 8 : ℝ) * (8 / A * x ^ (1 / 36 : ℝ)) =
        8 * (x ^ (5 / 8 : ℝ) * x ^ (1 / 36 : ℝ)) := by field_simp
    rw [he] at h
    nlinarith only [h, mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 8 * A)]
  have hgrowth : A * (⌊Real.sqrt (x * Real.log x)⌋₊ : ℝ) * (x ^ (49 / 72 : ℝ)) ^ 2 ≤
      x ^ 2 := by
    have he : Real.sqrt (x * Real.log x) * (x ^ (49 / 72 : ℝ)) ^ 2 =
        x ^ (67 / 36 : ℝ) * (Real.log x) ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul_natCast hx0.le]
      calc
        _ = (x ^ (1 / 2 : ℝ) * x ^ ((49 / 72 : ℝ) * 2)) *
          (Real.log x) ^ (1 / 2 : ℝ) := by ring
        _ = _ := by rw [← Real.rpow_add hx0]; norm_num
    have h := mul_le_mul_of_nonneg_left hg (by positivity : 0 ≤ A * x ^ (67 / 36 : ℝ))
    have he' : A * x ^ (67 / 36 : ℝ) * (1 / A * x ^ (5 / 36 : ℝ)) = x ^ 2 := by
      calc
        _ = x ^ (67 / 36 : ℝ) * x ^ (5 / 36 : ℝ) := by field_simp
        _ = _ := by rw [← Real.rpow_add hx0]; norm_num
    rw [he'] at h
    have hf := mul_le_mul_of_nonneg_left (Nat.floor_le (Real.sqrt_nonneg (x * Real.log x)))
      (by positivity : 0 ≤ A * (x ^ (49 / 72 : ℝ)) ^ 2)
    calc
      _ ≤ A * Real.sqrt (x * Real.log x) * (x ^ (49 / 72 : ℝ)) ^ 2 := by
        nlinarith only [hf]
      _ = A * x ^ (67 / 36 : ℝ) * (Real.log x) ^ (1 / 2 : ℝ) := by
        rw [mul_assoc, he, ← mul_assoc]
      _ ≤ _ := h
  exact ⟨hmnat, hlnat, hsnat, hqnat, hsnq, hgap, hc.1, hc.2.1, hmlog, hls, hR, hrad, hgrowth⟩

