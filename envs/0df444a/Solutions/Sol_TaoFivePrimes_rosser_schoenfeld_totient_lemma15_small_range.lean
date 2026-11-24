-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_totient_lemma15_small_range
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-22T10:24:31.093984+00:00
-- url     : https://prove2.me/submissions/ed798619-c33c-4754-b3c3-43b07973d957

import Definitions.Def_TaoFivePrimes_totient_cert_tables
import Definitions.Def_TaoFivePrimes_theta_cert_tables
import Theorems.Thm_TaoFivePrimes_tao_totient_cert_nth_prime_eq
import Theorems.Thm_TaoFivePrimes_tao_totient_cert_loglog_table
import Theorems.Thm_TaoFivePrimes_theta_cert_totient_gamma_lower
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_totient_lemma14
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
open Finset Real
set_option maxRecDepth 1000000
set_option maxHeartbeats 8000000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false

namespace TaoFivePrimes

private lemma t3_prod_ptab_Pnum (m : ℕ) (hm1 : 1 ≤ m) (hm65 : m ≤ 65) :
    (∏ i ∈ Finset.range m, ptab i) = Pnum m := by
  interval_cases m <;> decide

private lemma t3_prod_ptab_sub_1_Pden (m : ℕ) (hm1 : 1 ≤ m) (hm65 : m ≤ 65) :
    (∏ i ∈ Finset.range m, (ptab i - 1)) = Pden m := by
  interval_cases m <;> decide

private lemma t3_prod_Q_eq_Qpt (m : ℕ) (hm1 : 1 ≤ m) (hm65 : m ≤ 65) :
    (∏ i ∈ Finset.range m, (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1))
      = (Qpt m : ℝ) := by
  have hcast : ∀ i ∈ Finset.range m, (Nat.nth Nat.Prime i : ℝ) = (ptab i : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [tao_totient_cert_nth_prime_eq i (by omega : i < 66)]
  rw [show (∏ i ∈ Finset.range m, (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1))
        = ∏ i ∈ Finset.range m, (ptab i : ℝ) / ((ptab i : ℝ) - 1) by
      exact Finset.prod_congr rfl (fun i hi => by rw [hcast i hi])]
  have hsub : ∀ i ∈ Finset.range m, (ptab i : ℝ) - 1 = ((ptab i - 1 : ℕ) : ℝ) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 : 1 ≤ ptab i := by
      rw [← tao_totient_cert_nth_prime_eq i (by omega : i < 66)]
      exact (Nat.prime_nth_prime i).one_lt.le
    simpa using (Nat.cast_sub h1).symm
  rw [show (∏ i ∈ Finset.range m, (ptab i : ℝ) / ((ptab i : ℝ) - 1))
        = ∏ i ∈ Finset.range m, (ptab i : ℝ) / (((ptab i - 1 : ℕ) : ℝ)) by
      exact Finset.prod_congr rfl (fun i hi => by rw [hsub i hi])]
  rw [Finset.prod_div_distrib]
  rw [← Nat.cast_prod, ← Nat.cast_prod]
  rw [t3_prod_ptab_Pnum m hm1 hm65, t3_prod_ptab_sub_1_Pden m hm1 hm65]
  simp [Qpt]

private lemma t3_exp_gamma_ge : (178107237/10^8 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
  calc (178107237/10^8 : ℝ)
      ≤ ∑ i ∈ Finset.range 12, (57721565/10^8:ℝ)^i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp (57721565/10^8) := Real.sum_le_exp_of_nonneg (by norm_num) 12
    _ ≤ Real.exp Real.eulerMascheroniConstant := Real.exp_le_exp.mpr theta_cert_totient_gamma_lower

private lemma t3_mono (A c s t : ℝ) (hA : 0 < A) (hc : 0 < c)
    (hs : 3/2 ≤ s) (ht : 3/2 ≤ t) (hst : s ≤ t) (hAst : c ≤ A*(s*t)) :
    A*s + c/s ≤ A*t + c/t := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have h : A*t + c/t - (A*s + c/s) = (t - s) * (A*s*t - c) / (s*t) := by
    field_simp
    ring
  have h0 : 0 ≤ A*t + c/t - (A*s + c/s) := by
    rw [h]
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (by positivity)
  linarith

private lemma t3_amgm (A c t : ℝ) (hA : 0 < A) (hc : 0 < c) (ht : 0 < t) :
    2 * Real.sqrt (A*c) ≤ A*t + c/t := by
  have hsq : 4*(A*c) ≤ (A*t + c/t)^2 := by
    have h : (A*t + c/t)^2 = 4*(A*c) + (A*t - c/t)^2 := by
      field_simp
      ring
    nlinarith [sq_nonneg (A*t - c/t)]
  calc 2 * Real.sqrt (A*c) = Real.sqrt (4*(A*c)) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        rw [show Real.sqrt (4:ℝ) = 2 by
          rw [show (4:ℝ) = 2^2 by norm_num]
          exact Real.sqrt_sq (by norm_num)]
    _ ≤ Real.sqrt ((A*t + c/t)^2) := Real.sqrt_le_sqrt hsq
    _ = A*t + c/t := Real.sqrt_sq (by positivity)

private lemma t3_check25 (m : ℕ) (hm4 : 4 ≤ m) (hm61 : m ≤ 61) (hm9 : m ≠ 9) :
    (Qpt m : ℚ) < (rll m : ℚ) * (178107237/10^8) + (5/2)/(rll m : ℚ) := by
  rcases Nat.lt_or_ge m 9 with h | h
  · interval_cases m <;> norm_num [rll, Qpt, Pnum, Pden]
  · rcases Nat.lt_or_ge m 10 with h10 | h10
    · have hm9' : m = 9 := by omega
      subst hm9'
      exact absurd rfl hm9
    · interval_cases m <;> norm_num [rll, Qpt, Pnum, Pden]

theorem solution (n : ℕ) (y : ℝ) (hn : 1 < n)
    (h1 : 2.88 ≤ Real.log (n : ℝ) + y)
    (h2 : Real.log (n : ℝ) < Chebyshev.theta (Real.log (n : ℝ) + y))
    (h3 : 0 ≤ y - 2)
    (h4 : y - 2 ≤ 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))
    (h5 : Real.log (n : ℝ) + y - 2 < 286) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        5 / (2 * Real.log (Real.log (n : ℝ))) := by
  set t : ℝ := Real.log (n : ℝ) + y with ht
  set L : ℝ := Real.log (Real.log (n : ℝ)) with hL
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hw61 : n < primorial (Nat.nth Nat.Prime 61) := by
    have ht288 : t < 288 := by linarith
    have hexp : (n : ℝ) < Real.exp (Chebyshev.theta 293) := by
      have h2' : Chebyshev.theta t ≤ Chebyshev.theta 293 :=
        Chebyshev.theta_mono (by linarith : t ≤ 293)
      calc (n : ℝ) = Real.exp (Real.log (n : ℝ)) := (Real.exp_log hnpos).symm
        _ < Real.exp (Chebyshev.theta t) := Real.exp_lt_exp.mpr h2
        _ ≤ Real.exp (Chebyshev.theta 293) := Real.exp_le_exp.mpr h2'
    have h293 : Real.exp (Chebyshev.theta 293)
        = ((primorial (Nat.nth Nat.Prime 61) : ℕ) : ℝ) := by
      rw [Chebyshev.theta_eq_log_primorial]
      rw [show ⌊(293 : ℝ)⌋₊ = 293 by norm_num]
      rw [Real.exp_log (by exact_mod_cast (primorial_pos 293))]
      rw [tao_totient_cert_nth_prime_eq 61 (by norm_num : 61 < 66),
        show ptab 61 = 293 by decide]
    rw [h293] at hexp
    exact_mod_cast hexp
  have hex : ∃ j, n < primorial (Nat.nth Nat.Prime j) := ⟨61, hw61⟩
  obtain ⟨m, hm, hmin⟩ : ∃ m : ℕ, n < primorial (Nat.nth Nat.Prime m) ∧
      ∀ j, j < m → ¬ n < primorial (Nat.nth Nat.Prime j) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  have h1m : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    rw [hm0] at hm
    have hpr2 : primorial (Nat.nth Nat.Prime 0) = 2 := by
      rw [tao_totient_cert_nth_prime_eq 0 (by norm_num : 0 < 66)]
      decide
    rw [hpr2] at hm
    omega
  have hm61 : m ≤ 61 := by
    by_contra h
    exact hmin 61 (by omega) hw61
  have hQ : (n : ℝ) / Nat.totient n ≤ (Qpt m : ℝ) := by
    have hexp_m : (n : ℝ) < Real.exp (Chebyshev.theta (Nat.nth Nat.Prime m)) := by
      have heq : Real.exp (Chebyshev.theta (Nat.nth Nat.Prime m))
          = ((primorial (Nat.nth Nat.Prime m) : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast]
        exact Real.exp_log (by exact_mod_cast (primorial_pos _))
      rw [heq]
      exact_mod_cast hm
    have h14 := rosser_schoenfeld_totient_lemma14 n m (by omega) h1m hexp_m
    rwa [t3_prod_Q_eq_Qpt m h1m (by omega : m ≤ 65)] at h14
  by_cases hm3 : m ≤ 3
  · have hQ15 : (Qpt m : ℝ) ≤ 15/4 := by interval_cases m <;> norm_num [Qpt, Pnum, Pden]
    have hn3 : 3 ≤ n := by
      by_contra h
      have hn2 : n = 2 := by omega
      subst hn2
      have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hlog2lt1 : Real.log 2 < 1 := by
        have h2e : (2 : ℝ) < Real.exp 1 :=
          lt_trans (by norm_num : (2 : ℝ) < 2.7182818283) Real.exp_one_gt_d9
        have h := Real.log_lt_log (by norm_num : (0 : ℝ) < 2) h2e
        rwa [Real.log_exp] at h
      have hloglog2neg : Real.log (Real.log 2) < 0 := Real.log_neg hlog2pos hlog2lt1
      have hLneg : L < 0 := by rw [hL]; exact hloglog2neg
      have hRHSL : 0.9 * Real.log 2 / L < 0 :=
        div_neg_of_pos_of_neg (by positivity) hLneg
      linarith
    have hLpos : 0 < L := by
      have hn3R : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
      have hlog3 : Real.log 3 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn3R
      have h1' : (1 : ℝ) < Real.log 3 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
        linarith [Real.exp_one_lt_d9]
      rw [hL]
      exact Real.log_pos (by linarith)
    have hlt : (15/4 : ℝ) < 2 * Real.sqrt ((178107237/10^8)*(5/2)) := by
      rw [show (2 : ℝ) * Real.sqrt ((178107237/10^8)*(5/2))
          = Real.sqrt (4*((178107237/10^8)*(5/2))) by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        rw [show Real.sqrt (4:ℝ) = 2 by
          rw [show (4:ℝ) = 2^2 by norm_num]
          exact Real.sqrt_sq (by norm_num)]]
      rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 15/4)]
      norm_num
    calc (n : ℝ) / Nat.totient n ≤ (Qpt m : ℝ) := hQ
      _ ≤ 15/4 := hQ15
      _ < 2 * Real.sqrt ((178107237/10^8)*(5/2)) := hlt
      _ ≤ (178107237/10^8) * L + (5/2)/L :=
          t3_amgm (178107237/10^8) (5/2) L (by norm_num) (by norm_num) hLpos
      _ ≤ Real.exp Real.eulerMascheroniConstant * L + (5/2)/L := by
          have h1'' : (178107237/10^8) * L ≤ Real.exp Real.eulerMascheroniConstant * L :=
            mul_le_mul t3_exp_gamma_ge le_rfl (le_of_lt hLpos)
              (le_trans (by norm_num : (0:ℝ) ≤ 178107237/10^8) t3_exp_gamma_ge)
          linarith
      _ = Real.exp Real.eulerMascheroniConstant * L + 5/(2*L) := by ring
  · simp only [not_le] at hm3
    have hm4 : 4 ≤ m := by omega
    by_cases hm9 : m = 9
    · subst hm9
      have h223n : (223092870 : ℕ) ≤ n := by
        have hp1 : primorial (Nat.nth Nat.Prime 8) ≤ n := by
          have h := hmin 8 (by omega : 8 < 9)
          omega
        have hpr : primorial (Nat.nth Nat.Prime 8) = 223092870 := by
          rw [tao_totient_cert_nth_prime_eq 8 (by norm_num : 8 < 66)]
          decide
        omega
      have hn16 : (16 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 16 ≤ n)
      have hle223 : Real.log 223092870 ≤ Real.log (n : ℝ) := by
        apply Real.log_le_log (by norm_num : (0 : ℝ) < 223092870)
        exact_mod_cast h223n
      have hlogn16 : (16 : ℝ) ≤ Real.log (n : ℝ) := by
        rw [Real.le_log_iff_exp_le hnpos]
        calc Real.exp 16 = (Real.exp 1)^16 := by
              calc Real.exp 16 = Real.exp (((16 : ℕ) : ℝ) * 1) := by norm_num
                _ = (Real.exp 1)^16 := Real.exp_nat_mul 1 16
          _ ≤ (223092870 : ℝ) := by
              have hlt' : (Real.exp 1)^16 < (223092870 : ℝ) :=
                lt_of_lt_of_le
                  (pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le
                    (by norm_num : (16 : ℕ) ≠ 0))
                  (by norm_num)
              exact le_of_lt hlt'
          _ ≤ (n : ℝ) := by exact_mod_cast h223n
      have hL277 : (277/100 : ℝ) ≤ L := by
        have hlog416 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
          rw [show (16 : ℝ) = 2^4 by norm_num, Real.log_pow]
          norm_num
        have h := Real.log_le_log (by norm_num : (0 : ℝ) < 16) hlogn16
        rw [hL]
        calc (277/100 : ℝ) ≤ 4 * Real.log 2 := by linarith [Real.log_two_gt_d9]
          _ = Real.log 16 := hlog416.symm
          _ ≤ Real.log (Real.log (n : ℝ)) := h
      have ht29 : (29 : ℝ) ≤ t := by
        by_contra hcon
        simp only [not_le] at hcon
        have hθle : Chebyshev.theta t ≤ Real.log 223092870 := by
          calc Chebyshev.theta t = Chebyshev.theta (⌊t⌋₊ : ℝ) :=
                Chebyshev.theta_eq_theta_coe_floor t
            _ ≤ Chebyshev.theta 28 := by
                apply Chebyshev.theta_mono
                have hfloor : ⌊t⌋₊ ≤ 28 := by
                  have h : ⌊t⌋₊ < 29 := (Nat.floor_lt (by linarith : (0 : ℝ) ≤ t)).mpr hcon
                  omega
                exact_mod_cast hfloor
            _ = Real.log 223092870 := by
                rw [Chebyshev.theta_eq_log_primorial]
                rw [show ⌊(28 : ℝ)⌋₊ = 28 by norm_num]
                rw [show primorial 28 = 223092870 by decide]
                norm_num
        linarith
      have h27 : (27 : ℝ) ≤ Real.log (n : ℝ) * (1 + 0.9/L) := by
        have hty : t = Real.log (n : ℝ) + y := ht
        have hy : (29 : ℝ) - Real.log (n : ℝ) ≤ y := by linarith
        have key : (27 : ℝ) - Real.log (n : ℝ) ≤ 0.9 * Real.log (n : ℝ) / L := by
          have h4' : y - 2 ≤ 0.9 * Real.log (n : ℝ) / L := h4
          linarith
        have key2 : (27 : ℝ) ≤ Real.log (n : ℝ) + 0.9 * Real.log (n : ℝ) / L := by
          linarith
        have hEq : Real.log (n : ℝ) + 0.9 * Real.log (n : ℝ) / L
            = Real.log (n : ℝ) * (1 + 0.9/L) := by ring
        linarith
      have h367 : 1 + 0.9/L ≤ (367/277 : ℝ) := by
        have h1' : (0.9 : ℝ)/L ≤ 0.9/(277/100) :=
          div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 0.9)
            (by norm_num : (0:ℝ) < 277/100) hL277
        have h2' : (0.9 : ℝ)/(277/100) = 90/277 := by norm_num
        linarith
      have hlogn_ge : (7479/367 : ℝ) ≤ Real.log (n : ℝ) := by
        have h1' : Real.log (n : ℝ) * (1 + 0.9/L) ≤ Real.log (n : ℝ) * (367/277) :=
          mul_le_mul_of_nonneg_left h367 (by linarith : (0:ℝ) ≤ Real.log (n : ℝ))
        have h2' : (27 : ℝ) ≤ Real.log (n : ℝ) * (367/277) := le_trans h27 h1'
        have h3' : (27 : ℝ) * (277/367) ≤ Real.log (n : ℝ) := by
          have h := mul_le_mul_of_nonneg_right h2' (by norm_num : (0:ℝ) ≤ 277/367)
          have hc : Real.log (n : ℝ) * (367/277) * (277/367) = Real.log (n : ℝ) := by
            ring_nf
          linarith
        have h4' : (27 : ℝ) * (277/367) = 7479/367 := by norm_num
        linarith
      have hL3 : (3 : ℝ) ≤ L := by
        have he3 : Real.exp 3 ≤ (7479/367 : ℝ) := by
          have h' : (Real.exp 1)^3 < (7479/367 : ℝ) :=
            lt_of_lt_of_le
              (pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le
                (by norm_num : (3 : ℕ) ≠ 0))
              (by norm_num)
          calc Real.exp 3 = (Real.exp 1)^3 := by
                calc Real.exp 3 = Real.exp (((3 : ℕ) : ℝ) * 1) := by norm_num
                  _ = (Real.exp 1)^3 := Real.exp_nat_mul 1 3
            _ ≤ 7479/367 := le_of_lt h'
        have he3' : Real.exp 3 ≤ Real.log (n : ℝ) := le_trans he3 hlogn_ge
        calc (3 : ℝ) = Real.log (Real.exp 3) := (Real.log_exp 3).symm
          _ ≤ Real.log (Real.log (n : ℝ)) := Real.log_le_log (Real.exp_pos 3) he3'
          _ = L := hL.symm
      have hQ9 : (Qpt 9 : ℝ) < (178107237/10^8) * 3 + (5/2)/3 := by
        norm_num [Qpt, Pnum, Pden]
      calc (n : ℝ) / Nat.totient n ≤ (Qpt 9 : ℝ) := hQ
        _ < (178107237/10^8) * 3 + (5/2)/3 := hQ9
        _ ≤ Real.exp Real.eulerMascheroniConstant * 3 + (5/2)/3 := by
            have h1' : (178107237/10^8) * 3
                ≤ Real.exp Real.eulerMascheroniConstant * 3 :=
              mul_le_mul_of_nonneg_right t3_exp_gamma_ge (by norm_num)
            linarith
        _ ≤ Real.exp Real.eulerMascheroniConstant * L + (5/2)/L := by
            refine t3_mono (Real.exp Real.eulerMascheroniConstant) (5/2) 3 L
              (Real.exp_pos _) (by norm_num) (by norm_num)
              (le_trans (by norm_num : (3/2 : ℝ) ≤ 3) hL3) hL3 ?_
            have h1' : (5/2 : ℝ) ≤ (178107237/10^8) * (3 * 3) := by norm_num
            have h2' : (178107237/10^8) * (3 * 3)
                ≤ Real.exp Real.eulerMascheroniConstant * (3 * L) := by
              have h9L : (9 : ℝ) ≤ 3 * L := by linarith
              calc (178107237/10^8) * (3 * 3)
                  ≤ Real.exp Real.eulerMascheroniConstant * 9 :=
                    mul_le_mul t3_exp_gamma_ge (by norm_num) (by norm_num) (by positivity)
                _ ≤ Real.exp Real.eulerMascheroniConstant * (3 * L) :=
                    mul_le_mul_of_nonneg_left h9L (Real.exp_pos _).le
            linarith
        _ = Real.exp Real.eulerMascheroniConstant * L + 5/(2*L) := by ring
    · have hT2 := tao_totient_cert_loglog_table (m-1)
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [Nat.sub_add_cancel h1m] at hT2
      have hLlo : (rll m : ℝ) ≤ L := by
        have hp1 : primorial (Nat.nth Nat.Prime (m-1)) ≤ n := by
          have h := hmin (m-1) (by omega : m-1 < m)
          omega
        have hcast : ((primorial (Nat.nth Nat.Prime (m-1)) : ℕ) : ℝ) ≤ (n:ℝ) := by
          exact_mod_cast hp1
        have hlog1 : Real.log ((primorial (Nat.nth Nat.Prime (m-1)) : ℕ) : ℝ)
            ≤ Real.log (n:ℝ) :=
          Real.log_le_log (by exact_mod_cast (primorial_pos _)) hcast
        have hP2 : (1:ℝ) < ((primorial (Nat.nth Nat.Prime (m-1)) : ℕ) : ℝ) := by
          have hp2 : 2 ≤ Nat.nth Nat.Prime (m-1) := (Nat.prime_nth_prime (m-1)).two_le
          have hmono := primorial_mono hp2
          have hpr2 : primorial 2 = 2 := by decide
          have : 2 ≤ primorial (Nat.nth Nat.Prime (m-1)) := by omega
          exact_mod_cast (by omega : 1 < primorial (Nat.nth Nat.Prime (m-1)))
        have hlog2 : Real.log (Real.log ((primorial (Nat.nth Nat.Prime (m-1)) : ℕ) : ℝ))
            ≤ Real.log (Real.log (n:ℝ)) :=
          Real.log_le_log (Real.log_pos hP2) hlog1
        rw [hL]
        exact hT2.trans hlog2
      have hrllm : (3/2:ℝ) ≤ (rll m : ℝ) := by
        interval_cases m <;> norm_num [rll]
      have hck : (Qpt m : ℝ) <
          (rll m : ℝ) * (178107237/10^8) + (5/2)/(rll m : ℝ) := by
        have h0 := t3_check25 m hm4 hm61 hm9
        have h0R := (Rat.cast_lt (K := ℝ)).mpr h0
        push_cast at h0R
        exact h0R
      have hmono := t3_mono (Real.exp Real.eulerMascheroniConstant) (5/2) (rll m) L
        (Real.exp_pos _) (by norm_num) hrllm (le_trans hrllm hLlo) hLlo
        (by
          have hs : (3/2:ℝ) ≤ (rll m:ℝ) := hrllm
          have ht : (3/2:ℝ) ≤ L := le_trans hrllm hLlo
          have hst : (3/2:ℝ)*(3/2) ≤ (rll m:ℝ)*L :=
            mul_le_mul hs ht (by norm_num) (by linarith)
          have h1' : (178107237/10^8) * ((3/2)*(3/2)) ≤
              Real.exp Real.eulerMascheroniConstant * ((rll m)*L) :=
            mul_le_mul t3_exp_gamma_ge hst (by norm_num)
              (le_trans (by norm_num : (0:ℝ) ≤ 178107237/10^8) t3_exp_gamma_ge)
          have h2' : (5/2:ℝ) ≤ (178107237/10^8) * ((3/2)*(3/2)) := by norm_num
          linarith)
      calc (n:ℝ)/Nat.totient n ≤ (Qpt m : ℝ) := hQ
        _ < (rll m : ℝ) * (178107237/10^8) + (5/2)/(rll m : ℝ) := hck
        _ ≤ Real.exp Real.eulerMascheroniConstant * (rll m) + (5/2)/(rll m) := by
            have h1' : (rll m : ℝ) * (178107237/10^8)
                ≤ (rll m : ℝ) * Real.exp Real.eulerMascheroniConstant :=
              mul_le_mul_of_nonneg_left t3_exp_gamma_ge (by linarith [hrllm])
            linarith
        _ ≤ Real.exp Real.eulerMascheroniConstant * L + (5/2)/L := hmono
        _ = Real.exp Real.eulerMascheroniConstant * L + 5/(2*L) := by ring

end TaoFivePrimes

open TaoFivePrimes

/-- Root re-export for the verification harness. -/
theorem solution (n : ℕ) (y : ℝ) (hn : 1 < n)
    (h1 : 2.88 ≤ Real.log (n : ℝ) + y)
    (h2 : Real.log (n : ℝ) < Chebyshev.theta (Real.log (n : ℝ) + y))
    (h3 : 0 ≤ y - 2)
    (h4 : y - 2 ≤ 0.9 * Real.log (n : ℝ) / Real.log (Real.log (n : ℝ)))
    (h5 : Real.log (n : ℝ) + y - 2 < 286) :
    (n : ℝ) / Nat.totient n <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
        5 / (2 * Real.log (Real.log (n : ℝ))) :=
  TaoFivePrimes.solution n y hn h1 h2 h3 h4 h5

#print axioms solution
