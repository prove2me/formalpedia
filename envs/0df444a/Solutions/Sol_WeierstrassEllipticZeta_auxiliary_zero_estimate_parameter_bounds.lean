-- Prove2me | solution 1 for WeierstrassEllipticZeta.auxiliary_zero_estimate_parameter_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T01:39:14.818471+00:00
-- url     : https://prove2.me/submissions/6cfede93-f96b-4b31-8f17-45b667dc672f

import Theorems.Thm_WeierstrassEllipticZeta_auxiliary_parameter_estimates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option maxHeartbeats 600000

open Filter

open WeierstrassEllipticZeta

private theorem p2m_eventual_long_side_le_degree :
    ∀ᶠ N : ℕ in atTop, auxiliaryS3 N ≤ auxiliaryL0 N := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop 2
    (by norm_num : 0 < (3 / 8 : ℝ))).bound (by norm_num : 0 < (64 : ℝ))
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  filter_upwards [hn.eventually hsmall, hn.eventually (eventually_ge_atTop (2 : ℝ))]
    with N hsmall hN
  have hx : 0 < (N : ℝ) := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hsmall' : (Real.log N) ^ 2 ≤ 64 * (N : ℝ) ^ (3 / 8 : ℝ) := by
    simpa only [Real.rpow_two, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log N)),
      abs_of_nonneg (Real.rpow_nonneg hx.le _)] using hsmall
  have hpow : (N : ℝ) ^ (5 / 8 : ℝ) * (N : ℝ) ^ (3 / 8 : ℝ) = N := by
    rw [← Real.rpow_add hx]
    norm_num
  apply Nat.floor_mono
  apply (le_div_iff₀ hlog).mpr
  have hb := mul_le_mul_of_nonneg_left hsmall'
    (by positivity : 0 ≤ (N : ℝ) ^ (5 / 8 : ℝ))
  nlinarith only [hb, hpow]

theorem solution (C : ℝ) (hC : 0 < C) :
    ∃ k : ℕ, 3 ≤ k ∧ ∀ᶠ N : ℕ in atTop,
      let m := auxiliaryL0 N
      let l := auxiliaryL N
      let s := auxiliaryS N
      let q := auxiliaryS3 N
      1 ≤ m ∧ 1 ≤ l ∧ 1 ≤ s ∧ 1 ≤ q ∧ s ≤ q ∧ q ≤ m ∧ l ≤ m ∧
      3 ≤ k * m ∧
      3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
        (k * m : ℕ) * (s : ℝ) ^ 2 * q := by
  obtain ⟨k, hk⟩ := exists_nat_gt (691200 * C + 3)
  have hk3 : 3 ≤ k := by
    have : (3 : ℝ) < k := by nlinarith
    exact_mod_cast this.le
  refine ⟨k, hk3, ?_⟩
  filter_upwards [auxiliary_parameter_estimates 1 (by norm_num),
    p2m_eventual_long_side_le_degree, eventually_ge_atTop 2] with N hN hqm hN2
  rcases hN with ⟨hm, hl, hs, hq, hsq, _, hlo, _, hmlog, hls, _⟩
  let m := auxiliaryL0 N
  let l := auxiliaryL N
  let s := auxiliaryS N
  let q := auxiliaryS3 N
  have hlm : l ≤ m := by
    have hs1 : 1 ≤ s ^ 2 := one_le_pow₀ (by omega : 1 ≤ s)
    exact (Nat.le_mul_of_pos_right l hs1).trans hls
  have hkm : 3 ≤ k * m := hk3.trans (Nat.le_mul_of_pos_right k hm)
  refine ⟨hm, hl, by omega, hq, hsq, hqm, hlm, hkm, ?_⟩
  change 3 * C * max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) <
    (k * m : ℕ) * (s : ℝ) ^ 2 * q
  have hx : 0 < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hlreal : (l : ℝ) ≤ Real.sqrt ((N : ℝ) * Real.log N) :=
    Nat.floor_le (Real.sqrt_nonneg _)
  have hlsq : (l : ℝ) ^ 2 ≤ (N : ℝ) * Real.log N := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg l) hlreal 2
    rwa [Real.sq_sqrt (by positivity)] at hh
  have hmlsq : (m : ℝ) * (l : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by
    have h₁ := mul_le_mul_of_nonneg_left hlsq (Nat.cast_nonneg m)
    have h₂ := mul_le_mul_of_nonneg_left hmlog hx.le
    nlinarith only [h₁, h₂]
  have hdegree : max ((m : ℝ) * (15 * l) ^ 2) ((q : ℝ) * (15 * l) ^ 2) ≤
      225 * (N : ℝ) ^ 2 := by
    have hqmreal : (q : ℝ) ≤ m := by exact_mod_cast hqm
    have h₁ : (m : ℝ) * (15 * l) ^ 2 ≤ 225 * (N : ℝ) ^ 2 := by
      nlinarith only [hmlsq]
    exact max_le h₁ ((mul_le_mul_of_nonneg_right hqmreal (sq_nonneg _)).trans h₁)
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgrid : (N : ℝ) ^ 2 ≤ 1024 * (m : ℝ) * (s : ℝ) ^ 2 * q := by
    have h₁ := mul_le_mul_of_nonneg_right (by linarith : (m : ℝ) + 1 ≤ 2 * m)
      (by positivity : 0 ≤ (s : ℝ) ^ 2 * q)
    change (N : ℝ) ^ 2 / 512 ≤ ((m : ℝ) + 1) * (s : ℝ) ^ 2 * q at hlo
    nlinarith only [hlo, h₁]
  have hvolume : 0 < (m : ℝ) * (s : ℝ) ^ 2 * q := by
    have hsreal : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
    have hqreal : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    positivity
  have hstrict := mul_lt_mul_of_pos_right (by linarith : 691200 * C < (k : ℝ)) hvolume
  have hleft := mul_le_mul_of_nonneg_left hdegree (by positivity : 0 ≤ 3 * C)
  have hright := mul_le_mul_of_nonneg_left hgrid (by positivity : 0 ≤ 675 * C)
  push_cast
  nlinarith only [hstrict, hleft, hright]

