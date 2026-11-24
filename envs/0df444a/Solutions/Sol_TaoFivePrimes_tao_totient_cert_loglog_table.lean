-- Prove2me | solution 1 for TaoFivePrimes.tao_totient_cert_loglog_table
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:07:10.753388+00:00
-- url     : https://prove2.me/submissions/dcd8bba8-0be3-42f1-ae6c-e8fa7df6ba39

import Definitions.Def_TaoFivePrimes_totient_cert_tables
import Theorems.Thm_TaoFivePrimes_tao_totient_cert_nth_prime_eq
import Theorems.Thm_TaoFivePrimes_tao_totient_cert_ptab_mem
import Theorems.Thm_TaoFivePrimes_tao_totient_cert_primorial_nth
import Theorems.Thm_TaoFivePrimes_theta_cert_clbZ_le_log
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic
open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option exponentiation.threshold 4096
set_option linter.unnecessarySimpa false

namespace TaoFivePrimes

lemma prod_ptab_eq (k : ℕ) (hk : k ≤ 64) :
    (∏ i ∈ Finset.range (k+1), Nat.nth Nat.Prime i) = ∏ i ∈ Finset.range (k+1), ptab i :=
  Finset.prod_congr rfl (fun i hi => by
    rw [Finset.mem_range] at hi
    exact tao_totient_cert_nth_prime_eq i (by omega : i < 66))

lemma primorial_eq_ptab_prod (k : ℕ) (hk : k ≤ 64) :
    primorial (Nat.nth Nat.Prime k) = ∏ i ∈ Finset.range (k+1), ptab i := by
  rw [tao_totient_cert_primorial_nth k]
  exact prod_ptab_eq k hk

/-- Exponential certificate: if `exp 1 < 2.7182818286` and the truncated exponential
series at `f` (with remainder) is at most `U`, then `exp (a + f) ≤ U`. -/
lemma exp_cert_le (a : ℕ) (f U : ℝ) (h0 : 0 ≤ f) (h1 : f ≤ 1)
    (h : (2.7182818286:ℝ)^a * (∑ j ∈ Finset.range 12, f^j / j.factorial +
          f^12 * ((12:ℝ)+1) / ((Nat.factorial 12 : ℝ) * (12:ℝ))) ≤ U) :
    Real.exp ((a:ℝ) + f) ≤ U := by
  have hb := Real.exp_bound' h0 h1 (n := 12) (by norm_num)
  have hpow : (Real.exp 1)^a ≤ (2.7182818286:ℝ)^a :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_d9) a
  calc Real.exp ((a:ℝ) + (f:ℝ))
      = (Real.exp 1)^a * Real.exp f := by
        rw [Real.exp_add]
        congr 1
        simpa using (Real.exp_nat_mul (1:ℝ) a)
    _ ≤ (2.7182818286:ℝ)^a * (∑ j ∈ Finset.range 12, f^j / j.factorial +
          f^12 * ((12:ℝ)+1) / ((Nat.factorial 12 : ℝ) * (12:ℝ))) :=
        mul_le_mul hpow hb (le_of_lt (Real.exp_pos _)) (by positivity)
    _ ≤ U := h

/-- The certified log-log table for the primorials. -/
theorem solution (k : ℕ) (hk : k ∈ Finset.Icc 3 64) :
    (rll (k+1) : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime k) : ℝ)) := by
  have hk64 : k ≤ 64 := (Finset.mem_Icc.mp hk).2
  have hk3 : 3 ≤ k := (Finset.mem_Icc.mp hk).1
  interval_cases k
  · -- k = 3
    change (rll 4 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 3) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 3) = 210 := by
      rw [primorial_eq_ptab_prod 3 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 210))).mpr ?_
    have c1 : Real.exp (rll 4 : ℝ) ≤ (534627473/100000000 : ℝ) := by
      rw [show (rll 4 : ℝ) = ((1:ℕ):ℝ) + (1691/2500:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 1 (1691/2500 : ℝ) (534627473/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (534627473/100000000 : ℝ) ≤ Real.log (210:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 210)).mpr ?_
      rw [show (534627473/100000000:ℝ) = (5:ℝ) + (34627473/100000000:ℝ) by norm_num]
      exact exp_cert_le 5 (34627473/100000000 : ℝ) (210 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 4
    change (rll 5 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 4) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 4) = 2310 := by
      rw [primorial_eq_ptab_prod 4 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 2310))).mpr ?_
    have c1 : Real.exp (rll 5 : ℝ) ≤ (774385793/100000000 : ℝ) := by
      rw [show (rll 5 : ℝ) = (2:ℝ) + (469/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 2 (469/10000 : ℝ) (774385793/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (774385793/100000000 : ℝ) ≤ Real.log (2310:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2310)).mpr ?_
      rw [show (774385793/100000000:ℝ) = (7:ℝ) + (74385793/100000000:ℝ) by norm_num]
      exact exp_cert_le 7 (74385793/100000000 : ℝ) (2310 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 5
    change (rll 6 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 5) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 5) = 30030 := by
      rw [primorial_eq_ptab_prod 5 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 30030))).mpr ?_
    have c1 : Real.exp (rll 6 : ℝ) ≤ (515389543/50000000 : ℝ) := by
      rw [show (rll 6 : ℝ) = (2:ℝ) + (3329/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 2 (3329/10000 : ℝ) (515389543/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (515389543/50000000 : ℝ) ≤ Real.log (30030:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 30030)).mpr ?_
      rw [show (515389543/50000000:ℝ) = (10:ℝ) + (15389543/50000000:ℝ) by norm_num]
      exact exp_cert_le 10 (15389543/50000000 : ℝ) (30030 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 6
    change (rll 7 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 6) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 6) = 510510 := by
      rw [primorial_eq_ptab_prod 6 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 510510))).mpr ?_
    have c1 : Real.exp (rll 7 : ℝ) ≤ (1314051233/100000000 : ℝ) := by
      rw [show (rll 7 : ℝ) = (2:ℝ) + (5757/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 2 (5757/10000 : ℝ) (1314051233/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (1314051233/100000000 : ℝ) ≤ Real.log (510510:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 510510)).mpr ?_
      rw [show (1314051233/100000000:ℝ) = (13:ℝ) + (14051233/100000000:ℝ) by norm_num]
      exact exp_cert_le 13 (14051233/100000000 : ℝ) (510510 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 7
    change (rll 8 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 7) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 7) = 9699690 := by
      rw [primorial_eq_ptab_prod 7 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 9699690))).mpr ?_
    have c1 : Real.exp (rll 8 : ℝ) ≤ (100532541/6250000 : ℝ) := by
      rw [show (rll 8 : ℝ) = (2:ℝ) + (7779/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 2 (7779/10000 : ℝ) (100532541/6250000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (100532541/6250000 : ℝ) ≤ Real.log (9699690:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 9699690)).mpr ?_
      rw [show (100532541/6250000:ℝ) = (16:ℝ) + (532541/6250000:ℝ) by norm_num]
      exact exp_cert_le 16 (532541/6250000 : ℝ) (9699690 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 8
    change (rll 9 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 8) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 8) = 223092870 := by
      rw [primorial_eq_ptab_prod 8 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 223092870))).mpr ?_
    have c1 : Real.exp (rll 9 : ℝ) ≤ (240288731/12500000 : ℝ) := by
      rw [show (rll 9 : ℝ) = (2:ℝ) + (4780563/5000000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 2 (4780563/5000000 : ℝ) (240288731/12500000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (240288731/12500000 : ℝ) ≤ Real.log (223092870:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 223092870)).mpr ?_
      rw [show (240288731/12500000:ℝ) = (19:ℝ) + (2788731/12500000:ℝ) by norm_num]
      exact exp_cert_le 19 (2788731/12500000 : ℝ) (223092870 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 9
    change (rll 10 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 9) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 9) = 6469693230 := by
      rw [primorial_eq_ptab_prod 9 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 6469693230))).mpr ?_
    have c1 : Real.exp (rll 10 : ℝ) ≤ (2258757557/100000000 : ℝ) := by
      rw [show (rll 10 : ℝ) = (3:ℝ) + (587/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 3 (587/5000 : ℝ) (2258757557/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (2258757557/100000000 : ℝ) ≤ Real.log (6469693230:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 6469693230)).mpr ?_
      rw [show (2258757557/100000000:ℝ) = (22:ℝ) + (58757557/100000000:ℝ) by norm_num]
      exact exp_cert_le 22 (58757557/100000000 : ℝ) (6469693230 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 10
    change (rll 11 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 10) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 10) = 200560490130 := by
      rw [primorial_eq_ptab_prod 10 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 200560490130))).mpr ?_
    have c1 : Real.exp (rll 11 : ℝ) ≤ (650522461/25000000 : ℝ) := by
      rw [show (rll 11 : ℝ) = (3:ℝ) + (2589/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 3 (2589/10000 : ℝ) (650522461/25000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (650522461/25000000 : ℝ) ≤ Real.log (200560490130:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 200560490130)).mpr ?_
      rw [show (650522461/25000000:ℝ) = (26:ℝ) + (522461/25000000:ℝ) by norm_num]
      exact exp_cert_le 26 (522461/25000000 : ℝ) (200560490130 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 11
    change (rll 12 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 11) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 11) = 7420738134810 := by
      rw [primorial_eq_ptab_prod 11 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 7420738134810))).mpr ?_
    have c1 : Real.exp (rll 12 : ℝ) ≤ (2963037451/100000000 : ℝ) := by
      rw [show (rll 12 : ℝ) = (3:ℝ) + (243/625:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 3 (243/625 : ℝ) (2963037451/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (2963037451/100000000 : ℝ) ≤ Real.log (7420738134810:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 7420738134810)).mpr ?_
      rw [show (2963037451/100000000:ℝ) = (29:ℝ) + (63037451/100000000:ℝ) by norm_num]
      exact exp_cert_le 29 (63037451/100000000 : ℝ) (7420738134810 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 12
    change (rll 13 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 12) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 12) = 304250263527210 := by
      rw [primorial_eq_ptab_prod 12 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 304250263527210))).mpr ?_
    have c1 : Real.exp (rll 13 : ℝ) ≤ (26675791/800000 : ℝ) := by
      rw [show (rll 13 : ℝ) = (3:ℝ) + (5069/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 3 (5069/10000 : ℝ) (26675791/800000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (26675791/800000 : ℝ) ≤ Real.log (304250263527210:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 304250263527210)).mpr ?_
      rw [show (26675791/800000:ℝ) = (33:ℝ) + (275791/800000:ℝ) by norm_num]
      exact exp_cert_le 33 (275791/800000 : ℝ) (304250263527210 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 13
    change (rll 14 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 13) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 13) = 13082761331670030 := by
      rw [primorial_eq_ptab_prod 13 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 13082761331670030))).mpr ?_
    have c1 : Real.exp (rll 14 : ℝ) ≤ (185515403/5000000 : ℝ) := by
      rw [show (rll 14 : ℝ) = (3:ℝ) + (6137/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 3 (6137/10000 : ℝ) (185515403/5000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (185515403/5000000 : ℝ) ≤ Real.log (13082761331670030:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 13082761331670030)).mpr ?_
      rw [show (185515403/5000000:ℝ) = (37:ℝ) + (515403/5000000:ℝ) by norm_num]
      exact exp_cert_le 37 (515403/5000000 : ℝ) (13082761331670030 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 14
    change (rll 15 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 14) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 14) = 614889782588491410 := by
      rw [primorial_eq_ptab_prod 14 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 614889782588491410))).mpr ?_
    have c1 : Real.exp (rll 15 : ℝ) ≤ (2047598673/50000000 : ℝ) := by
      rw [show (rll 15 : ℝ) = (3:ℝ) + (1781/2500:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 3 (1781/2500 : ℝ) (2047598673/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (2047598673/50000000 : ℝ) ≤ Real.log (614889782588491410:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 614889782588491410)).mpr ?_
      rw [show (2047598673/50000000:ℝ) = (40:ℝ) + (47598673/50000000:ℝ) by norm_num]
      exact exp_cert_le 40 (47598673/50000000 : ℝ) (614889782588491410 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 15
    change (rll 16 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 15) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 15) = 32589158477190044730 := by
      rw [primorial_eq_ptab_prod 15 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 32589158477190044730))).mpr ?_
    have c1 : Real.exp (rll 16 : ℝ) ≤ (2246037893/50000000 : ℝ) := by
      rw [show (rll 16 : ℝ) = (3:ℝ) + (8049/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 3 (8049/10000 : ℝ) (2246037893/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (2246037893/50000000 : ℝ) ≤ Real.log (32589158477190044730:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 32589158477190044730)).mpr ?_
      rw [show (2246037893/50000000:ℝ) = (44:ℝ) + (46037893/50000000:ℝ) by norm_num]
      exact exp_cert_le 44 (46037893/50000000 : ℝ) (32589158477190044730 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 16
    change (rll 17 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 16) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 16) = 1922760350154212639070 := by
      rw [primorial_eq_ptab_prod 16 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 1922760350154212639070))).mpr ?_
    have c1 : Real.exp (rll 17 : ℝ) ≤ (2449950273/50000000 : ℝ) := by
      rw [show (rll 17 : ℝ) = (3:ℝ) + (4459/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 3 (4459/5000 : ℝ) (2449950273/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (2449950273/50000000 : ℝ) ≤ Real.log (1922760350154212639070:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 1922760350154212639070)).mpr ?_
      rw [show (2449950273/50000000:ℝ) = (48:ℝ) + (49950273/50000000:ℝ) by norm_num]
      exact exp_cert_le 48 (49950273/50000000 : ℝ) (1922760350154212639070 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 17
    change (rll 18 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 17) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 17) = 117288381359406970983270 := by
      rw [primorial_eq_ptab_prod 17 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 117288381359406970983270))).mpr ?_
    have c1 : Real.exp (rll 18 : ℝ) ≤ (5311184649/100000000 : ℝ) := by
      rw [show (rll 18 : ℝ) = (3:ℝ) + (2431/2500:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 3 (2431/2500 : ℝ) (5311184649/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (5311184649/100000000 : ℝ) ≤ Real.log (117288381359406970983270:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 117288381359406970983270)).mpr ?_
      rw [show (5311184649/100000000:ℝ) = (53:ℝ) + (11184649/100000000:ℝ) by norm_num]
      exact exp_cert_le 53 (11184649/100000000 : ℝ) (117288381359406970983270 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 18
    change (rll 19 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 18) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 18) = 7858321551080267055879090 := by
      rw [primorial_eq_ptab_prod 18 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 7858321551080267055879090))).mpr ?_
    have c1 : Real.exp (rll 19 : ℝ) ≤ (2865571273/50000000 : ℝ) := by
      rw [show (rll 19 : ℝ) = (4:ℝ) + (97/2000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (97/2000 : ℝ) (2865571273/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (2865571273/50000000 : ℝ) ≤ Real.log (7858321551080267055879090:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 7858321551080267055879090)).mpr ?_
      rw [show (2865571273/50000000:ℝ) = (57:ℝ) + (15571273/50000000:ℝ) by norm_num]
      exact exp_cert_le 57 (15571273/50000000 : ℝ) (7858321551080267055879090 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 19
    change (rll 20 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 19) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 19) = 557940830126698960967415390 := by
      rw [primorial_eq_ptab_prod 19 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 557940830126698960967415390))).mpr ?_
    have c1 : Real.exp (rll 20 : ℝ) ≤ (6157771287/100000000 : ℝ) := by
      rw [show (rll 20 : ℝ) = (4:ℝ) + (1203/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (1203/10000 : ℝ) (6157771287/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (6157771287/100000000 : ℝ) ≤ Real.log (557940830126698960967415390:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 557940830126698960967415390)).mpr ?_
      rw [show (6157771287/100000000:ℝ) = (61:ℝ) + (57771287/100000000:ℝ) by norm_num]
      exact exp_cert_le 61 (57771287/100000000 : ℝ) (557940830126698960967415390 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 20
    change (rll 21 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 20) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 20) = 40729680599249024150621323470 := by
      rw [primorial_eq_ptab_prod 20 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 40729680599249024150621323470))).mpr ?_
    have c1 : Real.exp (rll 21 : ℝ) ≤ (6586452633/100000000 : ℝ) := by
      rw [show (rll 21 : ℝ) = (4:ℝ) + (469/2500:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (469/2500 : ℝ) (6586452633/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (6586452633/100000000 : ℝ) ≤ Real.log (40729680599249024150621323470:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 40729680599249024150621323470)).mpr ?_
      rw [show (6586452633/100000000:ℝ) = (65:ℝ) + (86452633/100000000:ℝ) by norm_num]
      exact exp_cert_le 65 (86452633/100000000 : ℝ) (40729680599249024150621323470 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 21
    change (rll 22 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 21) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 21) = 3217644767340672907899084554130 := by
      rw [primorial_eq_ptab_prod 21 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 3217644767340672907899084554130))).mpr ?_
    have c1 : Real.exp (rll 22 : ℝ) ≤ (351158579/5000000 : ℝ) := by
      rw [show (rll 22 : ℝ) = (4:ℝ) + (1259/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (1259/5000 : ℝ) (351158579/5000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (351158579/5000000 : ℝ) ≤ Real.log (3217644767340672907899084554130:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 3217644767340672907899084554130)).mpr ?_
      rw [show (351158579/5000000:ℝ) = (70:ℝ) + (1158579/5000000:ℝ) by norm_num]
      exact exp_cert_le 70 (1158579/5000000 : ℝ) (3217644767340672907899084554130 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 22
    change (rll 23 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 22) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 22) = 267064515689275851355624017992790 := by
      rw [primorial_eq_ptab_prod 22 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 267064515689275851355624017992790))).mpr ?_
    have c1 : Real.exp (rll 23 : ℝ) ≤ (7464921447/100000000 : ℝ) := by
      rw [show (rll 23 : ℝ) = (4:ℝ) + (391/1250:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (391/1250 : ℝ) (7464921447/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (7464921447/100000000 : ℝ) ≤ Real.log (267064515689275851355624017992790:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 267064515689275851355624017992790)).mpr ?_
      rw [show (7464921447/100000000:ℝ) = (74:ℝ) + (64921447/100000000:ℝ) by norm_num]
      exact exp_cert_le 74 (64921447/100000000 : ℝ) (267064515689275851355624017992790 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 23
    change (rll 24 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 23) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 23) = 23768741896345550770650537601358310 := by
      rw [primorial_eq_ptab_prod 23 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 23768741896345550770650537601358310))).mpr ?_
    have c1 : Real.exp (rll 24 : ℝ) ≤ (1978463527/25000000 : ℝ) := by
      rw [show (rll 24 : ℝ) = (4:ℝ) + (232/625:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (232/625 : ℝ) (1978463527/25000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (1978463527/25000000 : ℝ) ≤ Real.log (23768741896345550770650537601358310:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 23768741896345550770650537601358310)).mpr ?_
      rw [show (1978463527/25000000:ℝ) = (79:ℝ) + (3463527/25000000:ℝ) by norm_num]
      exact exp_cert_le 79 (3463527/25000000 : ℝ) (23768741896345550770650537601358310 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 24
    change (rll 25 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 24) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 24) = 2305567963945518424753102147331756070 := by
      rw [primorial_eq_ptab_prod 24 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 2305567963945518424753102147331756070))).mpr ?_
    have c1 : Real.exp (rll 25 : ℝ) ≤ (2092836969/25000000 : ℝ) := by
      rw [show (rll 25 : ℝ) = (4:ℝ) + (2137/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (2137/5000 : ℝ) (2092836969/25000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (2092836969/25000000 : ℝ) ≤ Real.log (2305567963945518424753102147331756070:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2305567963945518424753102147331756070)).mpr ?_
      rw [show (2092836969/25000000:ℝ) = (83:ℝ) + (17836969/25000000:ℝ) by norm_num]
      exact exp_cert_le 83 (17836969/25000000 : ℝ) (2305567963945518424753102147331756070 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 25
    change (rll 26 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 25) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 25) = 232862364358497360900063316880507363070 := by
      rw [primorial_eq_ptab_prod 25 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 232862364358497360900063316880507363070))).mpr ?_
    have c1 : Real.exp (rll 26 : ℝ) ≤ (8833178431/100000000 : ℝ) := by
      rw [show (rll 26 : ℝ) = (4:ℝ) + (4811/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (4811/10000 : ℝ) (8833178431/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (8833178431/100000000 : ℝ) ≤ Real.log (232862364358497360900063316880507363070:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 232862364358497360900063316880507363070)).mpr ?_
      rw [show (8833178431/100000000:ℝ) = (88:ℝ) + (33178431/100000000:ℝ) by norm_num]
      exact exp_cert_le 88 (33178431/100000000 : ℝ) (232862364358497360900063316880507363070 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 26
    change (rll 27 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 26) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 26) = 23984823528925228172706521638692258396210 := by
      rw [primorial_eq_ptab_prod 26 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 23984823528925228172706521638692258396210))).mpr ?_
    have c1 : Real.exp (rll 27 : ℝ) ≤ (1859257093/20000000 : ℝ) := by
      rw [show (rll 27 : ℝ) = (4:ℝ) + (2661/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (2661/5000 : ℝ) (1859257093/20000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (1859257093/20000000 : ℝ) ≤ Real.log (23984823528925228172706521638692258396210:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 23984823528925228172706521638692258396210)).mpr ?_
      rw [show (1859257093/20000000:ℝ) = (92:ℝ) + (19257093/20000000:ℝ) by norm_num]
      exact exp_cert_le 92 (19257093/20000000 : ℝ) (23984823528925228172706521638692258396210 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 27
    change (rll 28 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 27) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 27) = 2566376117594999414479597815340071648394470 := by
      rw [primorial_eq_ptab_prod 27 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 2566376117594999414479597815340071648394470))).mpr ?_
    have c1 : Real.exp (rll 28 : ℝ) ≤ (4881574091/50000000 : ℝ) := by
      rw [show (rll 28 : ℝ) = (4:ℝ) + (1453/2500:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (1453/2500 : ℝ) (4881574091/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (4881574091/50000000 : ℝ) ≤ Real.log (2566376117594999414479597815340071648394470:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2566376117594999414479597815340071648394470)).mpr ?_
      rw [show (4881574091/50000000:ℝ) = (97:ℝ) + (31574091/50000000:ℝ) by norm_num]
      exact exp_cert_le 97 (31574091/50000000 : ℝ) (2566376117594999414479597815340071648394470 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 28
    change (rll 29 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 28) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 28) = 279734996817854936178276161872067809674997230 := by
      rw [primorial_eq_ptab_prod 28 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 279734996817854936178276161872067809674997230))).mpr ?_
    have c1 : Real.exp (rll 29 : ℝ) ≤ (1279121311/12500000 : ℝ) := by
      rw [show (rll 29 : ℝ) = (4:ℝ) + (3141/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (3141/5000 : ℝ) (1279121311/12500000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (1279121311/12500000 : ℝ) ≤ Real.log (279734996817854936178276161872067809674997230:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 279734996817854936178276161872067809674997230)).mpr ?_
      rw [show (1279121311/12500000:ℝ) = (102:ℝ) + (4121311/12500000:ℝ) by norm_num]
      exact exp_cert_le 102 (4121311/12500000 : ℝ) (279734996817854936178276161872067809674997230 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 29
    change (rll 30 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 29) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 29) = 31610054640417607788145206291543662493274686990 := by
      rw [primorial_eq_ptab_prod 29 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 31610054640417607788145206291543662493274686990))).mpr ?_
    have c1 : Real.exp (rll 30 : ℝ) ≤ (1070504267/10000000 : ℝ) := by
      rw [show (rll 30 : ℝ) = (4:ℝ) + (6733/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (6733/10000 : ℝ) (1070504267/10000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (1070504267/10000000 : ℝ) ≤ Real.log (31610054640417607788145206291543662493274686990:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 31610054640417607788145206291543662493274686990)).mpr ?_
      rw [show (1070504267/10000000:ℝ) = (107:ℝ) + (504267/10000000:ℝ) by norm_num]
      exact exp_cert_le 107 (504267/10000000 : ℝ) (31610054640417607788145206291543662493274686990 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 30
    change (rll 31 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 30) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 30) = 4014476939333036189094441199026045136645885247730 := by
      rw [primorial_eq_ptab_prod 30 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 4014476939333036189094441199026045136645885247730))).mpr ?_
    have c1 : Real.exp (rll 31 : ℝ) ≤ (1398742147/12500000 : ℝ) := by
      rw [show (rll 31 : ℝ) = (4:ℝ) + (897/1250:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (897/1250 : ℝ) (1398742147/12500000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (1398742147/12500000 : ℝ) ≤ Real.log (4014476939333036189094441199026045136645885247730:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 4014476939333036189094441199026045136645885247730)).mpr ?_
      rw [show (1398742147/12500000:ℝ) = (111:ℝ) + (11242147/12500000:ℝ) by norm_num]
      exact exp_cert_le 111 (11242147/12500000 : ℝ) (4014476939333036189094441199026045136645885247730 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 31
    change (rll 32 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 31) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 31) = 525896479052627740771371797072411912900610967452630 := by
      rw [primorial_eq_ptab_prod 31 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 525896479052627740771371797072411912900610967452630))).mpr ?_
    have c1 : Real.exp (rll 32 : ℝ) ≤ (5838463877/50000000 : ℝ) := by
      rw [show (rll 32 : ℝ) = (4:ℝ) + (3801/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (3801/5000 : ℝ) (5838463877/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (5838463877/50000000 : ℝ) ≤ Real.log (525896479052627740771371797072411912900610967452630:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 525896479052627740771371797072411912900610967452630)).mpr ?_
      rw [show (5838463877/50000000:ℝ) = (116:ℝ) + (38463877/50000000:ℝ) by norm_num]
      exact exp_cert_le 116 (38463877/50000000 : ℝ) (525896479052627740771371797072411912900610967452630 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 32
    change (rll 33 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 32) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 32) = 72047817630210000485677936198920432067383702541010310 := by
      rw [primorial_eq_ptab_prod 32 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 72047817630210000485677936198920432067383702541010310))).mpr ?_
    have c1 : Real.exp (rll 33 : ℝ) ≤ (3042320501/25000000 : ℝ) := by
      rw [show (rll 33 : ℝ) = (4:ℝ) + (1603/2000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (1603/2000 : ℝ) (3042320501/25000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (3042320501/25000000 : ℝ) ≤ Real.log (72047817630210000485677936198920432067383702541010310:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 72047817630210000485677936198920432067383702541010310)).mpr ?_
      rw [show (3042320501/25000000:ℝ) = (121:ℝ) + (17320501/25000000:ℝ) by norm_num]
      exact exp_cert_le 121 (17320501/25000000 : ℝ) (72047817630210000485677936198920432067383702541010310 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 33
    change (rll 34 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 33) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 33) = 10014646650599190067509233131649940057366334653200433090 := by
      rw [primorial_eq_ptab_prod 33 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 10014646650599190067509233131649940057366334653200433090))).mpr ?_
    have c1 : Real.exp (rll 34 : ℝ) ≤ (6331060309/50000000 : ℝ) := by
      rw [show (rll 34 : ℝ) = (4:ℝ) + (2103/2500:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (2103/2500 : ℝ) (6331060309/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (6331060309/50000000 : ℝ) ≤ Real.log (10014646650599190067509233131649940057366334653200433090:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 10014646650599190067509233131649940057366334653200433090)).mpr ?_
      rw [show (6331060309/50000000:ℝ) = (126:ℝ) + (31060309/50000000:ℝ) by norm_num]
      exact exp_cert_le 126 (31060309/50000000 : ℝ) (10014646650599190067509233131649940057366334653200433090 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 34
    change (rll 35 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 34) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 34) = 1492182350939279320058875736615841068547583863326864530410 := by
      rw [primorial_eq_ptab_prod 34 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 1492182350939279320058875736615841068547583863326864530410))).mpr ?_
    have c1 : Real.exp (rll 35 : ℝ) ≤ (6581533201/50000000 : ℝ) := by
      rw [show (rll 35 : ℝ) = (4:ℝ) + (22/25:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (22/25 : ℝ) (6581533201/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (6581533201/50000000 : ℝ) ≤ Real.log (1492182350939279320058875736615841068547583863326864530410:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 1492182350939279320058875736615841068547583863326864530410)).mpr ?_
      rw [show (6581533201/50000000:ℝ) = (131:ℝ) + (31533201/50000000:ℝ) by norm_num]
      exact exp_cert_le 131 (31533201/50000000 : ℝ) (1492182350939279320058875736615841068547583863326864530410 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 35
    change (rll 36 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 35) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 35) = 225319534991831177328890236228992001350685163362356544091910 := by
      rw [primorial_eq_ptab_prod 35 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 225319534991831177328890236228992001350685163362356544091910))).mpr ?_
    have c1 : Real.exp (rll 36 : ℝ) ≤ (341617173/2500000 : ℝ) := by
      rw [show (rll 36 : ℝ) = (4:ℝ) + (4587/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (4587/5000 : ℝ) (341617173/2500000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (341617173/2500000 : ℝ) ≤ Real.log (225319534991831177328890236228992001350685163362356544091910:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 225319534991831177328890236228992001350685163362356544091910)).mpr ?_
      rw [show (341617173/2500000:ℝ) = (136:ℝ) + (1617173/2500000:ℝ) by norm_num]
      exact exp_cert_le 136 (1617173/2500000 : ℝ) (225319534991831177328890236228992001350685163362356544091910 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 36
    change (rll 37 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 36) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 36) = 35375166993717494840635767087951744212057570647889977422429870 := by
      rw [primorial_eq_ptab_prod 36 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 35375166993717494840635767087951744212057570647889977422429870))).mpr ?_
    have c1 : Real.exp (rll 37 : ℝ) ≤ (14169827897/100000000 : ℝ) := by
      rw [show (rll 37 : ℝ) = (4:ℝ) + (9537/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (9537/10000 : ℝ) (14169827897/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (14169827897/100000000 : ℝ) ≤ Real.log (35375166993717494840635767087951744212057570647889977422429870:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 35375166993717494840635767087951744212057570647889977422429870)).mpr ?_
      rw [show (14169827897/100000000:ℝ) = (141:ℝ) + (69827897/100000000:ℝ) by norm_num]
      exact exp_cert_le 141 (69827897/100000000 : ℝ) (35375166993717494840635767087951744212057570647889977422429870 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 37
    change (rll 38 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 37) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 37) = 5766152219975951659023630035336134306565384015606066319856068810 := by
      rw [primorial_eq_ptab_prod 37 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 5766152219975951659023630035336134306565384015606066319856068810))).mpr ?_
    have c1 : Real.exp (rll 38 : ℝ) ≤ (14678956067/100000000 : ℝ) := by
      rw [show (rll 38 : ℝ) = (4:ℝ) + (989/1000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 4 (989/1000 : ℝ) (14678956067/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (14678956067/100000000 : ℝ) ≤ Real.log (5766152219975951659023630035336134306565384015606066319856068810:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 5766152219975951659023630035336134306565384015606066319856068810)).mpr ?_
      rw [show (14678956067/100000000:ℝ) = (146:ℝ) + (78956067/100000000:ℝ) by norm_num]
      exact exp_cert_le 146 (78956067/100000000 : ℝ) (5766152219975951659023630035336134306565384015606066319856068810 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 38
    change (rll 39 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 38) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 38) = 962947420735983927056946215901134429196419130606213075415963491270 := by
      rw [primorial_eq_ptab_prod 38 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 962947420735983927056946215901134429196419130606213075415963491270))).mpr ?_
    have c1 : Real.exp (rll 39 : ℝ) ≤ (759558933/5000000 : ℝ) := by
      rw [show (rll 39 : ℝ) = (5:ℝ) + (233/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (233/10000 : ℝ) (759558933/5000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (759558933/5000000 : ℝ) ≤ Real.log (962947420735983927056946215901134429196419130606213075415963491270:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 962947420735983927056946215901134429196419130606213075415963491270)).mpr ?_
      rw [show (759558933/5000000:ℝ) = (151:ℝ) + (4558933/5000000:ℝ) by norm_num]
      exact exp_cert_le 151 (4558933/5000000 : ℝ) (962947420735983927056946215901134429196419130606213075415963491270 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 39
    change (rll 40 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 39) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 39) = 166589903787325219380851695350896256250980509594874862046961683989710 := by
      rw [primorial_eq_ptab_prod 39 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 166589903787325219380851695350896256250980509594874862046961683989710))).mpr ?_
    have c1 : Real.exp (rll 40 : ℝ) ≤ (15705561857/100000000 : ℝ) := by
      rw [show (rll 40 : ℝ) = (5:ℝ) + (283/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (283/5000 : ℝ) (15705561857/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (15705561857/100000000 : ℝ) ≤ Real.log (166589903787325219380851695350896256250980509594874862046961683989710:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 166589903787325219380851695350896256250980509594874862046961683989710)).mpr ?_
      rw [show (15705561857/100000000:ℝ) = (157:ℝ) + (5561857/100000000:ℝ) by norm_num]
      exact exp_cert_le 157 (5561857/100000000 : ℝ) (166589903787325219380851695350896256250980509594874862046961683989710 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 40
    change (rll 41 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 40) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 40) = 29819592777931214269172453467810429868925511217482600306406141434158090 := by
      rw [primorial_eq_ptab_prod 40 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 29819592777931214269172453467810429868925511217482600306406141434158090))).mpr ?_
    have c1 : Real.exp (rll 41 : ℝ) ≤ (16224377709/100000000 : ℝ) := by
      rw [show (rll 41 : ℝ) = (5:ℝ) + (891/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (891/10000 : ℝ) (16224377709/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (16224377709/100000000 : ℝ) ≤ Real.log (29819592777931214269172453467810429868925511217482600306406141434158090:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 29819592777931214269172453467810429868925511217482600306406141434158090)).mpr ?_
      rw [show (16224377709/100000000:ℝ) = (162:ℝ) + (24377709/100000000:ℝ) by norm_num]
      exact exp_cert_le 162 (24377709/100000000 : ℝ) (29819592777931214269172453467810429868925511217482600306406141434158090 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 41
    change (rll 42 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 41) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 41) = 5397346292805549782720214077673687806275517530364350655459511599582614290 := by
      rw [primorial_eq_ptab_prod 41 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 5397346292805549782720214077673687806275517530364350655459511599582614290))).mpr ?_
    have c1 : Real.exp (rll 42 : ℝ) ≤ (4186313639/25000000 : ℝ) := by
      rw [show (rll 42 : ℝ) = (5:ℝ) + (1207/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (1207/10000 : ℝ) (4186313639/25000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (4186313639/25000000 : ℝ) ≤ Real.log (5397346292805549782720214077673687806275517530364350655459511599582614290:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 5397346292805549782720214077673687806275517530364350655459511599582614290)).mpr ?_
      rw [show (4186313639/25000000:ℝ) = (167:ℝ) + (11313639/25000000:ℝ) by norm_num]
      exact exp_cert_le 167 (11313639/25000000 : ℝ) (5397346292805549782720214077673687806275517530364350655459511599582614290 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 42
    change (rll 43 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 42) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 42) = 1030893141925860008499560888835674370998623848299590975192766715520279329390 := by
      rw [primorial_eq_ptab_prod 42 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 1030893141925860008499560888835674370998623848299590975192766715520279329390))).mpr ?_
    have c1 : Real.exp (rll 43 : ℝ) ≤ (17269033181/100000000 : ℝ) := by
      rw [show (rll 43 : ℝ) = (5:ℝ) + (303/2000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (303/2000 : ℝ) (17269033181/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (17269033181/100000000 : ℝ) ≤ Real.log (1030893141925860008499560888835674370998623848299590975192766715520279329390:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 1030893141925860008499560888835674370998623848299590975192766715520279329390)).mpr ?_
      rw [show (17269033181/100000000:ℝ) = (172:ℝ) + (69033181/100000000:ℝ) by norm_num]
      exact exp_cert_le 172 (69033181/100000000 : ℝ) (1030893141925860008499560888835674370998623848299590975192766715520279329390 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 43
    change (rll 44 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 43) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 43) = 198962376391690981640415251545285153602734402721821058212203976095413910572270 := by
      rw [primorial_eq_ptab_prod 43 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 198962376391690981640415251545285153602734402721821058212203976095413910572270))).mpr ?_
    have c1 : Real.exp (rll 44 : ℝ) ≤ (17794953539/100000000 : ℝ) := by
      rw [show (rll 44 : ℝ) = (5:ℝ) + (363/2000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (363/2000 : ℝ) (17794953539/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (17794953539/100000000 : ℝ) ≤ Real.log (198962376391690981640415251545285153602734402721821058212203976095413910572270:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 198962376391690981640415251545285153602734402721821058212203976095413910572270)).mpr ?_
      rw [show (17794953539/100000000:ℝ) = (177:ℝ) + (94953539/100000000:ℝ) by norm_num]
      exact exp_cert_le 177 (94953539/100000000 : ℝ) (198962376391690981640415251545285153602734402721821058212203976095413910572270 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 44
    change (rll 45 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 44) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 44) = 39195588149163123383161804554421175259738677336198748467804183290796540382737190 := by
      rw [primorial_eq_ptab_prod 44 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 39195588149163123383161804554421175259738677336198748467804183290796540382737190))).mpr ?_
    have c1 : Real.exp (rll 45 : ℝ) ≤ (18324059223/100000000 : ℝ) := by
      rw [show (rll 45 : ℝ) = (5:ℝ) + (527/2500:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (527/2500 : ℝ) (18324059223/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (18324059223/100000000 : ℝ) ≤ Real.log (39195588149163123383161804554421175259738677336198748467804183290796540382737190:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 39195588149163123383161804554421175259738677336198748467804183290796540382737190)).mpr ?_
      rw [show (18324059223/100000000:ℝ) = (183:ℝ) + (24059223/100000000:ℝ) by norm_num]
      exact exp_cert_le 183 (24059223/100000000 : ℝ) (39195588149163123383161804554421175259738677336198748467804183290796540382737190 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 45
    change (rll 46 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 45) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 45) = 7799922041683461553249199106329813876687996789903550945093032474868511536164700810 := by
      rw [primorial_eq_ptab_prod 45 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 7799922041683461553249199106329813876687996789903550945093032474868511536164700810))).mpr ?_
    have c1 : Real.exp (rll 46 : ℝ) ≤ (9426903987/50000000 : ℝ) := by
      rw [show (rll 46 : ℝ) = (5:ℝ) + (2393/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (2393/10000 : ℝ) (9426903987/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (9426903987/50000000 : ℝ) ≤ Real.log (7799922041683461553249199106329813876687996789903550945093032474868511536164700810:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 7799922041683461553249199106329813876687996789903550945093032474868511536164700810)).mpr ?_
      rw [show (9426903987/50000000:ℝ) = (188:ℝ) + (26903987/50000000:ℝ) by norm_num]
      exact exp_cert_le 188 (26903987/50000000 : ℝ) (7799922041683461553249199106329813876687996789903550945093032474868511536164700810 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 46
    change (rll 47 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 46) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 46) = 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 := by
      rw [primorial_eq_ptab_prod 46 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910))).mpr ?_
    have c1 : Real.exp (rll 47 : ℝ) ≤ (3877834951/20000000 : ℝ) := by
      rw [show (rll 47 : ℝ) = (5:ℝ) + (2673/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (2673/10000 : ℝ) (3877834951/20000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (3877834951/20000000 : ℝ) ≤ Real.log (1645783550795210387735581011435590727981167322669649249414629852197255934130751870910:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 1645783550795210387735581011435590727981167322669649249414629852197255934130751870910)).mpr ?_
      rw [show (3877834951/20000000:ℝ) = (193:ℝ) + (17834951/20000000:ℝ) by norm_num]
      exact exp_cert_le 193 (17834951/20000000 : ℝ) (1645783550795210387735581011435590727981167322669649249414629852197255934130751870910 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 47
    change (rll 48 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 47) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 47) = 367009731827331916465034565550136732339800312955331782619462457039988073311157667212930 := by
      rw [primorial_eq_ptab_prod 47 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 367009731827331916465034565550136732339800312955331782619462457039988073311157667212930))).mpr ?_
    have c1 : Real.exp (rll 48 : ℝ) ≤ (19929776263/100000000 : ℝ) := by
      rw [show (rll 48 : ℝ) = (5:ℝ) + (737/2500:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (737/2500 : ℝ) (19929776263/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (19929776263/100000000 : ℝ) ≤ Real.log (367009731827331916465034565550136732339800312955331782619462457039988073311157667212930:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 367009731827331916465034565550136732339800312955331782619462457039988073311157667212930)).mpr ?_
      rw [show (19929776263/100000000:ℝ) = (199:ℝ) + (29776263/100000000:ℝ) by norm_num]
      exact exp_cert_le 199 (29776263/100000000 : ℝ) (367009731827331916465034565550136732339800312955331782619462457039988073311157667212930 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 48
    change (rll 49 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 48) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 48) = 83311209124804345037562846379881038241134671040860314654617977748077292641632790457335110 := by
      rw [primorial_eq_ptab_prod 48 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 83311209124804345037562846379881038241134671040860314654617977748077292641632790457335110))).mpr ?_
    have c1 : Real.exp (rll 49 : ℝ) ≤ (2558889477/12500000 : ℝ) := by
      rw [show (rll 49 : ℝ) = (5:ℝ) + (201/625:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (201/625 : ℝ) (2558889477/12500000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (2558889477/12500000 : ℝ) ≤ Real.log (83311209124804345037562846379881038241134671040860314654617977748077292641632790457335110:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 83311209124804345037562846379881038241134671040860314654617977748077292641632790457335110)).mpr ?_
      rw [show (2558889477/12500000:ℝ) = (204:ℝ) + (8889477/12500000:ℝ) by norm_num]
      exact exp_cert_le 204 (8889477/12500000 : ℝ) (83311209124804345037562846379881038241134671040860314654617977748077292641632790457335110 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 49
    change (rll 50 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 49) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 49) = 19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190 := by
      rw [primorial_eq_ptab_prod 49 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190))).mpr ?_
    have c1 : Real.exp (rll 50 : ℝ) ≤ (21014546913/100000000 : ℝ) := by
      rw [show (rll 50 : ℝ) = (5:ℝ) + (1739/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (1739/5000 : ℝ) (21014546913/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (21014546913/100000000 : ℝ) ≤ Real.log (19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190)).mpr ?_
      rw [show (21014546913/100000000:ℝ) = (210:ℝ) + (14546913/100000000:ℝ) by norm_num]
      exact exp_cert_le 210 (14546913/100000000 : ℝ) (19078266889580195013601891820992757757219839668357012055907516904309700014933909014729740190 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 50
    change (rll 51 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 50) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 50) = 4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270 := by
      rw [primorial_eq_ptab_prod 50 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270))).mpr ?_
    have c1 : Real.exp (rll 51 : ℝ) ≤ (21559464499/100000000 : ℝ) := by
      rw [show (rll 51 : ℝ) = (5:ℝ) + (1867/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (1867/5000 : ℝ) (21559464499/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (21559464499/100000000 : ℝ) ≤ Real.log (4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270)).mpr ?_
      rw [show (21559464499/100000000:ℝ) = (215:ℝ) + (59464499/100000000:ℝ) by norm_num]
      exact exp_cert_le 215 (59464499/100000000 : ℝ) (4445236185272185438169240794291312557432222642727183809026451438704160103479600800432029464270 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 51
    change (rll 52 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 51) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 51) = 1062411448280052319722448549835623701226301211611796930357321893850294264731624591303255041960530 := by
      rw [primorial_eq_ptab_prod 51 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 1062411448280052319722448549835623701226301211611796930357321893850294264731624591303255041960530))).mpr ?_
    have c1 : Real.exp (rll 52 : ℝ) ≤ (2763431947/12500000 : ℝ) := by
      rw [show (rll 52 : ℝ) = (5:ℝ) + (797/2000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (797/2000 : ℝ) (2763431947/12500000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (2763431947/12500000 : ℝ) ≤ Real.log (1062411448280052319722448549835623701226301211611796930357321893850294264731624591303255041960530:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 1062411448280052319722448549835623701226301211611796930357321893850294264731624591303255041960530)).mpr ?_
      rw [show (2763431947/12500000:ℝ) = (221:ℝ) + (931947/12500000:ℝ) by norm_num]
      exact exp_cert_le 221 (931947/12500000 : ℝ) (1062411448280052319722448549835623701226301211611796930357321893850294264731624591303255041960530 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 52
    change (rll 53 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 52) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 52) = 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730 := by
      rw [primorial_eq_ptab_prod 52 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730))).mpr ?_
    have c1 : Real.exp (rll 53 : ℝ) ≤ (22655777757/100000000 : ℝ) := by
      rw [show (rll 53 : ℝ) = (5:ℝ) + (423/1000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (423/1000 : ℝ) (22655777757/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (22655777757/100000000 : ℝ) ≤ Real.log (256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730)).mpr ?_
      rw [show (22655777757/100000000:ℝ) = (226:ℝ) + (55777757/100000000:ℝ) by norm_num]
      exact exp_cert_le 226 (55777757/100000000 : ℝ) (256041159035492609053110100510385311995538591998443060216114576417920917800321526504084465112487730 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 53
    change (rll 54 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 53) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 53) = 64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230 := by
      rw [primorial_eq_ptab_prod 53 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230))).mpr ?_
    have c1 : Real.exp (rll 54 : ℝ) ≤ (23208414527/100000000 : ℝ) := by
      rw [show (rll 54 : ℝ) = (5:ℝ) + (4471/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (4471/10000 : ℝ) (23208414527/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (23208414527/100000000 : ℝ) ≤ Real.log (64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230)).mpr ?_
      rw [show (23208414527/100000000:ℝ) = (232:ℝ) + (8414527/100000000:ℝ) by norm_num]
      exact exp_cert_le 232 (8414527/100000000 : ℝ) (64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 54
    change (rll 55 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 54) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 54) = 16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110 := by
      rw [primorial_eq_ptab_prod 54 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110))).mpr ?_
    have c1 : Real.exp (rll 55 : ℝ) ≤ (23762647333/100000000 : ℝ) := by
      rw [show (rll 55 : ℝ) = (5:ℝ) + (4707/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (4707/10000 : ℝ) (23762647333/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (23762647333/100000000 : ℝ) ≤ Real.log (16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110)).mpr ?_
      rw [show (23762647333/100000000:ℝ) = (237:ℝ) + (62647333/100000000:ℝ) by norm_num]
      exact exp_cert_le 237 (62647333/100000000 : ℝ) (16516447045902521732188973253623425320896207954043566485360902980990824644545340710198976591011245999110 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 55
    change (rll 56 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 55) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 55) = 4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930 := by
      rw [primorial_eq_ptab_prod 55 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930))).mpr ?_
    have c1 : Real.exp (rll 56 : ℝ) ≤ (12160192749/50000000 : ℝ) := by
      rw [show (rll 56 : ℝ) = (5:ℝ) + (4939/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (4939/10000 : ℝ) (12160192749/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (12160192749/50000000 : ℝ) ≤ Real.log (4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930)).mpr ?_
      rw [show (12160192749/50000000:ℝ) = (243:ℝ) + (10192749/50000000:ℝ) by norm_num]
      exact exp_cert_le 243 (10192749/50000000 : ℝ) (4343825573072363215565699965702960859395702691913457985649917484000586881515424606782330843435957697765930 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 56
    change (rll 57 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 56) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 56) = 1168489079156465704987173290774096471177444024124720198139827803196157871127649219224446996884272620699035170 := by
      rw [primorial_eq_ptab_prod 56 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 1168489079156465704987173290774096471177444024124720198139827803196157871127649219224446996884272620699035170))).mpr ?_
    have c1 : Real.exp (rll 57 : ℝ) ≤ (24878771957/100000000 : ℝ) := by
      rw [show (rll 57 : ℝ) = (5:ℝ) + (2583/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (2583/5000 : ℝ) (24878771957/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (24878771957/100000000 : ℝ) ≤ Real.log (1168489079156465704987173290774096471177444024124720198139827803196157871127649219224446996884272620699035170:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 1168489079156465704987173290774096471177444024124720198139827803196157871127649219224446996884272620699035170)).mpr ?_
      rw [show (24878771957/100000000:ℝ) = (248:ℝ) + (78771957/100000000:ℝ) by norm_num]
      exact exp_cert_le 248 (78771957/100000000 : ℝ) (1168489079156465704987173290774096471177444024124720198139827803196157871127649219224446996884272620699035170 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 57
    change (rll 58 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 57) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 57) = 316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070 := by
      rw [primorial_eq_ptab_prod 57 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070))).mpr ?_
    have c1 : Real.exp (rll 58 : ℝ) ≤ (12719900397/50000000 : ℝ) := by
      rw [show (rll 58 : ℝ) = (5:ℝ) + (5389/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (5389/10000 : ℝ) (12719900397/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (12719900397/50000000 : ℝ) ≤ Real.log (316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070)).mpr ?_
      rw [show (12719900397/50000000:ℝ) = (254:ℝ) + (19900397/50000000:ℝ) by norm_num]
      exact exp_cert_le 254 (19900397/50000000 : ℝ) (316660540451402206051523961799780143689087330537799173695893334666158783075592938409825136155637880209438531070 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 58
    change (rll 59 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 58) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 58) = 87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390 := by
      rw [primorial_eq_ptab_prod 58 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390))).mpr ?_
    have c1 : Real.exp (rll 59 : ℝ) ≤ (13001538901/50000000 : ℝ) := by
      rw [show (rll 59 : ℝ) = (5:ℝ) + (701/1250:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (701/1250 : ℝ) (13001538901/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (13001538901/50000000 : ℝ) ≤ Real.log (87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390)).mpr ?_
      rw [show (13001538901/50000000:ℝ) = (260:ℝ) + (1538901/50000000:ℝ) by norm_num]
      exact exp_cert_le 260 (1538901/50000000 : ℝ) (87714969705038411076272137418539099801877190558970371113762453702525982911939243939521562715111692818014473106390 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 59
    change (rll 60 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 59) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 59) = 24647906487115793512432470614609487044327490547070674282967249490409801198254927547005559122946385681862066942895590 := by
      rw [primorial_eq_ptab_prod 59 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 24647906487115793512432470614609487044327490547070674282967249490409801198254927547005559122946385681862066942895590))).mpr ?_
    have c1 : Real.exp (rll 60 : ℝ) ≤ (26565540553/100000000 : ℝ) := by
      rw [show (rll 60 : ℝ) = (5:ℝ) + (2911/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (2911/5000 : ℝ) (26565540553/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (26565540553/100000000 : ℝ) ≤ Real.log (24647906487115793512432470614609487044327490547070674282967249490409801198254927547005559122946385681862066942895590:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 24647906487115793512432470614609487044327490547070674282967249490409801198254927547005559122946385681862066942895590)).mpr ?_
      rw [show (26565540553/100000000:ℝ) = (265:ℝ) + (65540553/100000000:ℝ) by norm_num]
      exact exp_cert_le 265 (65540553/100000000 : ℝ) (24647906487115793512432470614609487044327490547070674282967249490409801198254927547005559122946385681862066942895590 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 60
    change (rll 61 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 60) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 60) = 6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970 := by
      rw [primorial_eq_ptab_prod 60 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970))).mpr ?_
    have c1 : Real.exp (rll 61 : ℝ) ≤ (27129315827/100000000 : ℝ) := by
      rw [show (rll 61 : ℝ) = (5:ℝ) + (377/625:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (377/625 : ℝ) (27129315827/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (27129315827/100000000 : ℝ) ≤ Real.log (6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970)).mpr ?_
      rw [show (27129315827/100000000:ℝ) = (271:ℝ) + (29315827/100000000:ℝ) by norm_num]
      exact exp_cert_le 271 (29315827/100000000 : ℝ) (6975357535853769564018389183934484833544679824821000822079731605785973739106144495802573231793827147966964944839451970 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 61
    change (rll 62 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 61) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 61) = 2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210 := by
      rw [primorial_eq_ptab_prod 61 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210))).mpr ?_
    have c1 : Real.exp (rll 62 : ℝ) ≤ (13848372649/50000000 : ℝ) := by
      rw [show (rll 62 : ℝ) = (5:ℝ) + (6239/10000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (6239/10000 : ℝ) (13848372649/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (13848372649/50000000 : ℝ) ≤ Real.log (2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210)).mpr ?_
      rw [show (13848372649/50000000:ℝ) = (276:ℝ) + (48372649/50000000:ℝ) by norm_num]
      exact exp_cert_le 276 (48372649/50000000 : ℝ) (2043779758005154482257388030892804056228591188672553240869361360495290305558100337270153956915591354354320728837959427210 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 62
    change (rll 63 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 62) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 62) = 627440385707582426053018125484090845262177494922473844946893937672054123806336803541937264773086545786776463753253544153470 := by
      rw [primorial_eq_ptab_prod 62 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 627440385707582426053018125484090845262177494922473844946893937672054123806336803541937264773086545786776463753253544153470))).mpr ?_
    have c1 : Real.exp (rll 63 : ℝ) ≤ (3533798541/12500000 : ℝ) := by
      rw [show (rll 63 : ℝ) = (5:ℝ) + (1611/2500:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (1611/2500 : ℝ) (3533798541/12500000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (3533798541/12500000 : ℝ) ≤ Real.log (627440385707582426053018125484090845262177494922473844946893937672054123806336803541937264773086545786776463753253544153470:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 627440385707582426053018125484090845262177494922473844946893937672054123806336803541937264773086545786776463753253544153470)).mpr ?_
      rw [show (3533798541/12500000:ℝ) = (282:ℝ) + (8798541/12500000:ℝ) by norm_num]
      exact exp_cert_le 282 (8798541/12500000 : ℝ) (627440385707582426053018125484090845262177494922473844946893937672054123806336803541937264773086545786776463753253544153470 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 63
    change (rll 64 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 63) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 63) = 195133959955058134502488637025552252876537200920889365778484014616008832503770745901542489344429915739687480227261852231729170 := by
      rw [primorial_eq_ptab_prod 63 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 195133959955058134502488637025552252876537200920889365778484014616008832503770745901542489344429915739687480227261852231729170))).mpr ?_
    have c1 : Real.exp (rll 64 : ℝ) ≤ (28844372349/100000000 : ℝ) := by
      rw [show (rll 64 : ℝ) = (5:ℝ) + (1329/2000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (1329/2000 : ℝ) (28844372349/100000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (28844372349/100000000 : ℝ) ≤ Real.log (195133959955058134502488637025552252876537200920889365778484014616008832503770745901542489344429915739687480227261852231729170:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 195133959955058134502488637025552252876537200920889365778484014616008832503770745901542489344429915739687480227261852231729170)).mpr ?_
      rw [show (28844372349/100000000:ℝ) = (288:ℝ) + (44372349/100000000:ℝ) by norm_num]
      exact exp_cert_le 288 (44372349/100000000 : ℝ) (195133959955058134502488637025552252876537200920889365778484014616008832503770745901542489344429915739687480227261852231729170 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

  · -- k = 64
    change (rll 65 : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime 64) : ℝ))
    have hP : primorial (Nat.nth Nat.Prime 64) = 61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210 := by
      rw [primorial_eq_ptab_prod 64 (by norm_num)]
      decide
    rw [hP]
    refine (Real.le_log_iff_exp_le (Real.log_pos (by norm_num : (1:ℝ) < 61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210))).mpr ?_
    have c1 : Real.exp (rll 65 : ℝ) ≤ (14709120263/50000000 : ℝ) := by
      rw [show (rll 65 : ℝ) = (5:ℝ) + (3421/5000:ℝ) by simp only [rll]; norm_num]
      exact exp_cert_le 5 (3421/5000 : ℝ) (14709120263/50000000 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    have c2 : (14709120263/50000000 : ℝ) ≤ Real.log (61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210:ℝ) := by
      refine (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210)).mpr ?_
      rw [show (14709120263/50000000:ℝ) = (294:ℝ) + (9120263/50000000:ℝ) by norm_num]
      exact exp_cert_le 294 (9120263/50000000 : ℝ) (61076929465933196099278943388997855150356143888238371488665496574810764573680243467182799164806563626522181311132959748531230210 : ℝ) (by norm_num) (by norm_num) (by norm_num)
    exact c1.trans c2

end TaoFivePrimes

open TaoFivePrimes

/-- Root re-export for the verification harness. -/
theorem solution (k : ℕ) (hk : k ∈ Finset.Icc 3 64) :
    (rll (k+1) : ℝ) ≤ Real.log (Real.log (primorial (Nat.nth Nat.Prime k) : ℝ)) :=
  TaoFivePrimes.solution k hk

#print axioms solution
