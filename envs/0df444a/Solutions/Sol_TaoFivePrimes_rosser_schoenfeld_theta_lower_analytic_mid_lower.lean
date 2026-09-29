-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-24T13:29:26.909048+00:00
-- url     : https://prove2.me/submissions/d2605726-f319-458c-9f48-2ecf77bb6ed9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_finite
import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_large
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Reduction of `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower`

Target (Rosser--Schoenfeld 1962, Theorem 4, eq. (3.14), for `1420 <= t <= 10^9`):

    for every real t with 1420 <= t <= 10^9,   t * (1 - 1 / (2 log t)) < theta t.

The range is split at `10^8`, which is the **floor** of this method: it is the
hypothesis threshold of the published analytic input
`TaoFivePrimes.schoenfeld_psi_error_large`, `|psi t - t| <= t/(40 log t)`.

* `1420 <= t <= 10^8`: the platform child
  `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_finite`.
* `10^8 <= t <= 10^9`: the published `psi` input together with Mathlib's
  `Chebyshev.psi_sub_theta_le`, `psi t - theta t <= 2 sqrt t log t`.

Only the lower half `psi t >= t - t/(40 log t)` of the two-sided input is used.

The numerical core is `2 (log t)^2 < (19/40) sqrt t` on `10^8 <= t <= 10^9`,
proved in two regimes.

* `t <= 2^27`. Since `t = 2^26 * (t / 2^26)`, writing `z = t / 2^26 <= 2`,

      log t = 26 log 2 + log z <= 26 log 2 + z - 1 < 18.022 + 2 - 1 < 19.03,

  by `Real.log_two_lt_d9` and `Real.log_le_sub_one_of_pos`; and
  `sqrt t >= 10^4`. Hence `2 (log t)^2 < 2 * 19.03^2 = 724.3 < 4750 = (19/40) 10^4`.
* `t >= 2^27`. With four nested square roots, `t = u4^16`,
  `log t = 16 log u4 <= 16 u4` and `sqrt t = u3^4` where `u3 = t^(1/8)`, so
  `2 (log t)^2 <= 512 u3 < (19/40) u3^4` as soon as `u3^3 > 512/(19/40) = 1077.9`.
  From `t >= 2^27`, `sqrt t >= 11585`, then `sqrt (sqrt t) >= 107.6`, then
  `u3 >= 10.37`, and `10.37^3 = 1115.2 > 1077.9`.

Nothing else is assumed: the file has no `sorry`, no `axiom`, and imports only
the two platform nodes named above plus Mathlib.
-/

theorem solution (t : ℝ) (h1 : 1420 ≤ t) (h2 : t ≤ 10 ^ 9) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by
  by_cases hsmall : t ≤ 10 ^ 8
  · exact TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_finite t h1 hsmall
  · have hlo : (10 : ℝ) ^ 8 < t := not_le.mp hsmall
    have ht0 : (0 : ℝ) < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hconv : t * (1 - 1 / (2 * Real.log t)) = t - t / (2 * Real.log t) := by
      have h2' : (2 : ℝ) * Real.log t ≠ 0 := by positivity
      field_simp
    have hpsi := TaoFivePrimes.schoenfeld_psi_error_large t (le_of_lt hlo)
    have hpsi_low : t - t / (40 * Real.log t) ≤ Chebyshev.psi t := by
      have hab := abs_le.mp hpsi
      linarith [hab.1]
    have hcorr : Chebyshev.psi t - Chebyshev.theta t ≤ 2 * Real.sqrt t * Real.log t :=
      Chebyshev.psi_sub_theta_le (by linarith)
    have htheta_low :
        t - t / (40 * Real.log t) - 2 * Real.sqrt t * Real.log t ≤ Chebyshev.theta t := by
      linarith
    have hnum : 2 * (Real.log t) ^ 2 < (19 / 40) * Real.sqrt t := by
      by_cases hcut : t ≤ (2 : ℝ) ^ 27
      · -- regime 1: t <= 2^27
        have hp26 : (0 : ℝ) < (2 : ℝ) ^ 26 := by positivity
        have htdiv : (0 : ℝ) < t / (2 : ℝ) ^ 26 := by positivity
        have hsplit : Real.log t = 26 * Real.log 2 + Real.log (t / (2 : ℝ) ^ 26) := by
          have hmul : t = (2 : ℝ) ^ 26 * (t / (2 : ℝ) ^ 26) := by field_simp
          have h1 : Real.log t = Real.log ((2 : ℝ) ^ 26) + Real.log (t / (2 : ℝ) ^ 26) := by
            conv_lhs => rw [hmul]
            exact Real.log_mul (by positivity : ((2 : ℝ) ^ 26) ≠ 0)
              (by positivity : t / (2 : ℝ) ^ 26 ≠ 0)
          have h2 : Real.log ((2 : ℝ) ^ 26) = 26 * Real.log 2 := by
            rw [Real.log_pow]
            norm_num
          rw [h1, h2]
        have hle := Real.log_le_sub_one_of_pos htdiv
        have hlog2 := Real.log_two_lt_d9
        have htdiv2 : t / (2 : ℝ) ^ 26 ≤ 2 := by
          rw [div_le_iff₀ hp26]
          have hp27 : (2 : ℝ) * (2 : ℝ) ^ 26 = (2 : ℝ) ^ 27 := by norm_num
          rw [hp27]
          exact hcut
        have hlog_le : Real.log t ≤ 19.03 := by
          rw [hsplit]
          nlinarith [hle, hlog2, htdiv2]
        have hs : (10 : ℝ) ^ 4 ≤ Real.sqrt t := by
          refine Real.le_sqrt_of_sq_le ?_
          have hsq : (((10 : ℝ) ^ 4)) ^ 2 = (10 : ℝ) ^ 8 := by norm_num
          rw [hsq]
          linarith
        have hlognn : (0 : ℝ) ≤ Real.log t := le_of_lt hlogt
        have hsq2 : (Real.log t) ^ 2 ≤ (19.03 : ℝ) ^ 2 := by nlinarith [hlog_le, hlognn]
        nlinarith [hsq2, hs]
      · -- regime 2: t >= 2^27, four nested square roots
        have hbig : (2 : ℝ) ^ 27 < t := not_le.mp hcut
        have hu1 : (11585 : ℝ) ≤ Real.sqrt t := by
          refine Real.le_sqrt_of_sq_le ?_
          have hsq : ((11585 : ℝ)) ^ 2 = 134212225 := by norm_num
          have hp : (134212225 : ℝ) < (2 : ℝ) ^ 27 := by norm_num
          rw [hsq]
          linarith
        have hu2 : (107.6 : ℝ) ≤ Real.sqrt (Real.sqrt t) := by
          refine Real.le_sqrt_of_sq_le ?_
          have hsq : ((107.6 : ℝ)) ^ 2 = 11577.76 := by norm_num
          have hle : (11577.76 : ℝ) ≤ (11585 : ℝ) := by norm_num
          rw [hsq]
          linarith
        have hu3 : (10.37 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt t)) := by
          refine Real.le_sqrt_of_sq_le ?_
          have hsq : ((10.37 : ℝ)) ^ 2 = 107.5369 := by norm_num
          have hle : (107.5369 : ℝ) ≤ (107.6 : ℝ) := by norm_num
          rw [hsq]
          linarith
        have hu4pos : 0 < Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt t))) := by positivity
        have ht_eq : t = Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 16 := by
          have hh1 : Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 2 =
              Real.sqrt (Real.sqrt (Real.sqrt t)) := Real.sq_sqrt (Real.sqrt_nonneg _)
          have hh2 : Real.sqrt (Real.sqrt (Real.sqrt t)) ^ 2 = Real.sqrt (Real.sqrt t) :=
            Real.sq_sqrt (Real.sqrt_nonneg _)
          have hh3 : Real.sqrt (Real.sqrt t) ^ 2 = Real.sqrt t := Real.sq_sqrt (Real.sqrt_nonneg _)
          have hh4 : Real.sqrt t ^ 2 = t := Real.sq_sqrt (le_of_lt ht0)
          calc t = (((Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 2) ^ 2) ^ 2) ^ 2 := by
                rw [hh1, hh2, hh3, hh4]
            _ = Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 16 := by ring
        have hlog_eq : Real.log t =
            16 * Real.log (Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt t)))) := by
          have h := congrArg Real.log ht_eq
          rw [Real.log_pow] at h
          exact h
        have hlog_bound : Real.log t ≤ 16 * Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt t))) := by
          have hle := Real.log_le_sub_one_of_pos hu4pos
          rw [hlog_eq]
          linarith
        have hL2 : (Real.log t) ^ 2 ≤ 256 * Real.sqrt (Real.sqrt (Real.sqrt t)) := by
          have h4sq : Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 2 =
              Real.sqrt (Real.sqrt (Real.sqrt t)) := Real.sq_sqrt (Real.sqrt_nonneg _)
          have hnn : (0 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt (Real.sqrt t))) :=
            Real.sqrt_nonneg _
          have hlognn : (0 : ℝ) ≤ Real.log t := le_of_lt hlogt
          nlinarith [hlog_bound, h4sq, hnn, hlognn]
        have hApos : 0 < Real.sqrt (Real.sqrt (Real.sqrt t)) := by positivity
        have hsqrt_eq : Real.sqrt t = (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 4 := by
          have hh2 : Real.sqrt (Real.sqrt (Real.sqrt t)) ^ 2 = Real.sqrt (Real.sqrt t) :=
            Real.sq_sqrt (Real.sqrt_nonneg _)
          have hh3 : Real.sqrt (Real.sqrt t) ^ 2 = Real.sqrt t := Real.sq_sqrt (Real.sqrt_nonneg _)
          calc Real.sqrt t = ((Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 2) ^ 2 := by rw [hh2, hh3]
            _ = (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 4 := by ring
        have hcube : (10.37 : ℝ) ^ 3 ≤ (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 3 :=
          pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10.37) hu3 3
        have h512 : (512 : ℝ) < (19 / 40) * (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 3 := by
          have hmul : (19 / 40) * ((10.37 : ℝ)) ^ 3 ≤
              (19 / 40) * (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 3 :=
            mul_le_mul_of_nonneg_left hcube (by norm_num)
          have hval : (512 : ℝ) < (19 / 40) * ((10.37 : ℝ)) ^ 3 := by norm_num
          linarith [hmul, hval]
        have h512A : (512 : ℝ) * Real.sqrt (Real.sqrt (Real.sqrt t)) <
            (19 / 40) * (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 4 := by
          have hmul := mul_lt_mul_of_pos_right h512 hApos
          have heq : (19 / 40) * (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 3 *
              Real.sqrt (Real.sqrt (Real.sqrt t)) =
              (19 / 40) * (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 4 := by ring
          rw [heq] at hmul
          exact hmul
        rw [hsqrt_eq]
        nlinarith [hL2, h512A]
    have hm1 : 2 * Real.sqrt t * (Real.log t) ^ 2 < (19 / 40) * t := by
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
      have h := mul_lt_mul_of_pos_right hnum hs
      have hs2t : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (le_of_lt ht0)
      nlinarith [h, hs2t]
    have hm2 : 2 * Real.sqrt t * Real.log t < (19 / 40) * (t / Real.log t) := by
      rw [← mul_div_assoc]
      rw [lt_div_iff₀ hlogt]
      nlinarith [hm1]
    have hsum : t / (2 * Real.log t) - t / (40 * Real.log t) =
        (19 / 40) * (t / Real.log t) := by
      have h2' : (2 : ℝ) * Real.log t ≠ 0 := by positivity
      have h40 : (40 : ℝ) * Real.log t ≠ 0 := by positivity
      field_simp
      ring
    rw [hconv]
    linarith
