-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-24T12:51:51.927145+00:00
-- url     : https://prove2.me/submissions/f93df36e-97d5-43eb-a89a-1e7cdc12c82f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_mid_lower
import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_large
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Reduction of `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid`

Target (Rosser--Schoenfeld 1962, Theorem 4, eq. (3.14), middle range):

    for every real t with 1420 <= t <= 10^10,   t * (1 - 1 / (2 log t)) < theta t.

The range is split at `10^9`:

* `1420 <= t <= 10^9`: the new platform child
  `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower`.
* `10^9 <= t`: the published platform input
  `TaoFivePrimes.schoenfeld_psi_error_large`, i.e. `|psi t - t| <= t/(40 log t)`,
  together with Mathlib's `Chebyshev.psi_sub_theta_le`, which bounds the
  prime-power correction `psi t - theta t <= 2 sqrt t * log t`.

In the second case only the **lower** half `psi t >= t - t/(40 log t)` is used.
The numerical core is the elementary comparison

    2 (log t)^2 < (19/40) sqrt t    on  t >= 10^9,

proved as follows. With four nested square roots, write
`u4 = t^(1/16)`, `u3 = t^(1/8)`, `u1 = t^(1/2)`. Then `t = u4^16` and
`log t = 16 log u4 <= 16 u4` by `Real.log_le_sub_one_of_pos`, so
`(log t)^2 <= 256 u4^2 = 256 u3`. Also `sqrt t = u1 = u3^4`. Hence

    2 (log t)^2 <= 512 u3 < (19/40) u3^4 = (19/40) sqrt t,

where the middle inequality is `u3^3 > 512 / (19/40) = 1077.9`, which follows
from `u3 >= 13.3`; that in turn follows from `t >= 10^9` by
`31622 <= sqrt t`, `177 <= sqrt (sqrt t)`, `13.3 <= sqrt (sqrt (sqrt t))`.

Nothing else is assumed: the file has no `sorry`, no `axiom`, and imports only
the two platform nodes named above plus Mathlib.
-/

theorem solution (t : ℝ) (h1 : 1420 ≤ t) (h2 : t ≤ 10 ^ 10) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by
  by_cases hsmall : t ≤ 10 ^ 9
  · exact TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid_lower t h1 hsmall
  · have hbig : (10 : ℝ) ^ 9 < t := not_le.mp hsmall
    have ht0 : (0 : ℝ) < t := by linarith
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    have hconv : t * (1 - 1 / (2 * Real.log t)) = t - t / (2 * Real.log t) := by
      have h2' : (2 : ℝ) * Real.log t ≠ 0 := by positivity
      field_simp
    -- the explicit two-sided Chebyshev input, threshold 10^8 <= 10^9 < t
    have hpsi := TaoFivePrimes.schoenfeld_psi_error_large t (by
      have h8 : ((10 : ℝ) ^ 8 : ℝ) < (10 : ℝ) ^ 9 := by norm_num
      linarith)
    have hpsi_low : t - t / (40 * Real.log t) ≤ Chebyshev.psi t := by
      have hab := abs_le.mp hpsi
      linarith [hab.1]
    have hcorr : Chebyshev.psi t - Chebyshev.theta t ≤ 2 * Real.sqrt t * Real.log t :=
      Chebyshev.psi_sub_theta_le (by linarith)
    have htheta_low :
        t - t / (40 * Real.log t) - 2 * Real.sqrt t * Real.log t ≤ Chebyshev.theta t := by
      linarith
    -- u1 = t^(1/2), u2 = t^(1/4), u3 = t^(1/8), u4 = t^(1/16)
    have hu1 : (31622 : ℝ) ≤ Real.sqrt t := by
      refine Real.le_sqrt_of_sq_le ?_
      have hsq : ((31622 : ℝ)) ^ 2 = 999950884 := by norm_num
      have hten : (999950884 : ℝ) < (10 : ℝ) ^ 9 := by norm_num
      rw [hsq]
      linarith
    have hu2 : (177 : ℝ) ≤ Real.sqrt (Real.sqrt t) := by
      refine Real.le_sqrt_of_sq_le ?_
      have hsq : ((177 : ℝ)) ^ 2 = 31329 := by norm_num
      have hle : (31329 : ℝ) ≤ (31622 : ℝ) := by norm_num
      rw [hsq]
      linarith
    have hu3 : (13.3 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt t)) := by
      refine Real.le_sqrt_of_sq_le ?_
      have hsq : ((13.3 : ℝ)) ^ 2 = 176.89 := by norm_num
      have hle : (176.89 : ℝ) ≤ (177 : ℝ) := by norm_num
      rw [hsq]
      linarith
    -- log t <= 16 * t^(1/16)
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
    have hcube : (13.3 : ℝ) ^ 3 ≤ (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 3 :=
      pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 13.3) hu3 3
    have h512 : (512 : ℝ) < (19 / 40) * (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 3 := by
      have hmul : (19 / 40) * ((13.3 : ℝ)) ^ 3 ≤
          (19 / 40) * (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube (by norm_num)
      have hval : (512 : ℝ) < (19 / 40) * ((13.3 : ℝ)) ^ 3 := by norm_num
      linarith [hmul, hval]
    have hmain : 2 * (Real.log t) ^ 2 < (19 / 40) * Real.sqrt t := by
      rw [hsqrt_eq]
      have h512A : (512 : ℝ) * Real.sqrt (Real.sqrt (Real.sqrt t)) <
          (19 / 40) * (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 4 := by
        have hmul := mul_lt_mul_of_pos_right h512 hApos
        have heq : (19 / 40) * (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 3 *
            Real.sqrt (Real.sqrt (Real.sqrt t)) =
            (19 / 40) * (Real.sqrt (Real.sqrt (Real.sqrt t))) ^ 4 := by ring
        rw [heq] at hmul
        exact hmul
      nlinarith [hL2, h512A]
    have hm1 : 2 * Real.sqrt t * (Real.log t) ^ 2 < (19 / 40) * t := by
      have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
      have h := mul_lt_mul_of_pos_right hmain hs
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
