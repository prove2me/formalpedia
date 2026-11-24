-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-18T11:09:03.648841+00:00
-- url     : https://prove2.me/submissions/ee89c952-2fee-4da1-af76-f935fe76ac11

import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_finite
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_analytic_mid
import Theorems.Thm_TaoFivePrimes_schoenfeld_psi_error_large
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Reduction of `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic`

Target (Rosser--Schoenfeld 1962, Theorem 4, eq. (3.14)):

    for every real t >= 1340,   t * (1 - 1 / (2 log t)) < theta t.

The reduction splits the range on t:

* `1340 <= t <= 1420`: the already proved platform theorem
  `TaoFivePrimes.rosser_schoenfeld_theta_lower_finite` gives
  `t - 2 sqrt t < theta t`, and `t * (1 - 1/(2 log t)) <= t - 2 sqrt t`
  follows from `4 log t <= sqrt t` (proved here from `log 2 < 0.6931471808`
  and `1420 <= 2^11`).
* `1420 <= t <= 10^10`: the new child
  `TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid`.
* `10^10 <= t`: the published platform input
  `TaoFivePrimes.schoenfeld_psi_error_large` (the explicit two-sided
  Chebyshev bound `|psi t - t| <= t/(40 log t)`) combined with Mathlib's
  `Chebyshev.psi_sub_theta_le`, i.e. `psi t - theta t <= 2 sqrt t * log t`,
  which is the prime-power correction between the two Chebyshev functions.
  The numerical comparison `(19/40) sqrt t > 2 (log t)^2` on this range is
  proved from `log t <= 8 * t^(1/8)` (Mathlib's `Real.log_le_sub_one_of_pos`
  applied to the eighth root, written as three nested square roots).

Nothing else is assumed: the file has no `sorry`, no `axiom`, and imports
only the three platform nodes named above plus Mathlib.
-/

theorem solution (t : ℝ) (h1 : 1340 ≤ t) :
    t * (1 - 1 / (2 * Real.log t)) < Chebyshev.theta t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hconv : t * (1 - 1 / (2 * Real.log t)) = t - t / (2 * Real.log t) := by
    have h2 : (2 : ℝ) * Real.log t ≠ 0 := by positivity
    field_simp
  by_cases hsmall : t ≤ 1420
  · -- 1340 <= t <= 1420
    have hfin := TaoFivePrimes.rosser_schoenfeld_theta_lower_finite t (by linarith) hsmall
    have hlog_le : 4 * Real.log t ≤ Real.sqrt t := by
      have ha : Real.log t ≤ Real.log 1420 := Real.log_le_log ht0 hsmall
      have hb : Real.log 1420 ≤ Real.log ((2 : ℝ) ^ 11) :=
        Real.log_le_log (by norm_num) (by norm_num)
      have hc : Real.log ((2 : ℝ) ^ 11) = 11 * Real.log 2 := by
        rw [Real.log_pow]
        norm_num
      have hd : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
      have he : (36.6 : ℝ) ≤ Real.sqrt 1340 := by
        refine Real.le_sqrt_of_sq_le ?_
        norm_num
      have hf : Real.sqrt 1340 ≤ Real.sqrt t := Real.sqrt_le_sqrt (by linarith)
      linarith
    have hkey : 4 * Real.sqrt t * Real.log t ≤ t := by
      have h := mul_le_mul_of_nonneg_left hlog_le (Real.sqrt_nonneg t)
      have hs := Real.mul_self_sqrt (le_of_lt ht0)
      nlinarith [h, hs]
    have h2s : 2 * Real.sqrt t ≤ t / (2 * Real.log t) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [hkey]
    rw [hconv]
    linarith
  · have hbig : 1420 ≤ t := le_of_not_ge hsmall
    by_cases hmid : t ≤ (10 : ℝ) ^ 10
    · exact TaoFivePrimes.rosser_schoenfeld_theta_lower_analytic_mid t hbig hmid
    · -- t >= 10^10 : Schoenfeld's psi bound plus the prime-power correction
      have hhuge : (10 : ℝ) ^ 10 < t := not_le.mp hmid
      have hpsi := TaoFivePrimes.schoenfeld_psi_error_large t (by
        have h8 : ((10 : ℝ) ^ 8 : ℝ) ≤ (10 : ℝ) ^ 10 := by norm_num
        linarith)
      have hpsi_low : t - t / (40 * Real.log t) ≤ Chebyshev.psi t := by
        have hab := abs_le.mp hpsi
        linarith [hab.1]
      have hcorr : Chebyshev.psi t - Chebyshev.theta t ≤ 2 * Real.sqrt t * Real.log t :=
        Chebyshev.psi_sub_theta_le (by linarith)
      have htheta_low :
          t - t / (40 * Real.log t) - 2 * Real.sqrt t * Real.log t ≤ Chebyshev.theta t := by
        linarith
      -- numeric core: (19/40) * t / log t > 2 * sqrt t * log t on t >= 10^10
      have hs_t : (10 : ℝ) ^ 5 ≤ Real.sqrt t := by
        have h10 : ((10 : ℝ) ^ 5) ^ 2 ≤ t := by
          have : ((10 : ℝ) ^ 5) ^ 2 = (10 : ℝ) ^ 10 := by norm_num
          rw [this]
          linarith
        exact Real.le_sqrt_of_sq_le h10
      have hss_t : (269.5 : ℝ) ≤ Real.sqrt (Real.sqrt t) := by
        have h := Real.sqrt_le_sqrt hs_t
        have h269 : (269.5 : ℝ) ≤ Real.sqrt ((10 : ℝ) ^ 5) := by
          refine Real.le_sqrt_of_sq_le ?_
          norm_num
        exact le_trans h269 h
      have hlog_bound : Real.log t ≤ 8 * Real.sqrt (Real.sqrt (Real.sqrt t)) := by
        have hs0 : 0 < Real.sqrt (Real.sqrt (Real.sqrt t)) := by positivity
        have ht_eq : t = Real.sqrt (Real.sqrt (Real.sqrt t)) ^ 8 := by
          have h1 : Real.sqrt (Real.sqrt (Real.sqrt t)) ^ 2 = Real.sqrt (Real.sqrt t) :=
            Real.sq_sqrt (Real.sqrt_nonneg _)
          have h2 : Real.sqrt (Real.sqrt t) ^ 2 = Real.sqrt t :=
            Real.sq_sqrt (Real.sqrt_nonneg _)
          have h3 : Real.sqrt t ^ 2 = t := Real.sq_sqrt (le_of_lt ht0)
          calc t = ((Real.sqrt (Real.sqrt (Real.sqrt t)) ^ 2) ^ 2) ^ 2 := by rw [h1, h2, h3]
            _ = Real.sqrt (Real.sqrt (Real.sqrt t)) ^ 8 := by ring
        have hlog_eq : Real.log t = 8 * Real.log (Real.sqrt (Real.sqrt (Real.sqrt t))) := by
          have h := congrArg Real.log ht_eq
          rw [Real.log_pow] at h
          exact h
        have hle := Real.log_le_sub_one_of_pos hs0
        linarith
      have hL2 : (Real.log t) ^ 2 ≤ 64 * Real.sqrt (Real.sqrt t) := by
        have hs2 : Real.sqrt (Real.sqrt (Real.sqrt t)) ^ 2 = Real.sqrt (Real.sqrt t) :=
          Real.sq_sqrt (Real.sqrt_nonneg _)
        have hnn : (0 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt t)) := Real.sqrt_nonneg _
        have hlog_nn : (0 : ℝ) ≤ Real.log t := le_of_lt hlogt
        nlinarith [hlog_bound, hs2, hnn, hlog_nn]
      have hmain : 2 * (Real.log t) ^ 2 < (19 / 40) * Real.sqrt t := by
        have hs2 : Real.sqrt (Real.sqrt t) ^ 2 = Real.sqrt t := Real.sq_sqrt (Real.sqrt_nonneg _)
        have hpos : 0 < Real.sqrt (Real.sqrt t) := by positivity
        nlinarith [hL2, hs2, hpos, hss_t]
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
        have h2 : (2 : ℝ) * Real.log t ≠ 0 := by positivity
        have h40 : (40 : ℝ) * Real.log t ≠ 0 := by positivity
        field_simp
        ring
      rw [hconv]
      linarith
