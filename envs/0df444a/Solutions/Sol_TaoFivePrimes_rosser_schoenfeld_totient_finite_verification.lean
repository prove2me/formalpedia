-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_totient_finite_verification
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:16:30.741565+00:00
-- url     : https://prove2.me/submissions/08251a26-691a-4727-807f-dace4d53ed39

import Definitions.Def_TaoFivePrimes_totient_cert_tables
import Definitions.Def_TaoFivePrimes_theta_cert_tables
import Theorems.Thm_TaoFivePrimes_tao_totient_cert_nth_prime_eq
import Theorems.Thm_TaoFivePrimes_tao_totient_cert_ptab_mem
import Theorems.Thm_TaoFivePrimes_tao_totient_cert_primorial_nth
import Theorems.Thm_TaoFivePrimes_tao_totient_cert_loglog_table
import Theorems.Thm_TaoFivePrimes_tao_totient_cert_h_check
import Theorems.Thm_TaoFivePrimes_theta_cert_clbZ_le_log
import Theorems.Thm_TaoFivePrimes_theta_cert_totient_gamma_lower
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

lemma t3_prod_ptab_Pnum (m : ℕ) (hm1 : 1 ≤ m) (hm65 : m ≤ 65) :
    (∏ i ∈ Finset.range m, ptab i) = Pnum m := by
  interval_cases m <;> decide

lemma t3_prod_ptab_sub_1_Pden (m : ℕ) (hm1 : 1 ≤ m) (hm65 : m ≤ 65) :
    (∏ i ∈ Finset.range m, (ptab i - 1)) = Pden m := by
  interval_cases m <;> decide

lemma t3_prod_Q_eq_Qpt (m : ℕ) (hm1 : 1 ≤ m) (hm65 : m ≤ 65) :
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

lemma Snum_le_log (k : ℕ) (hk : k ≤ 65) :
    (Snum (k+1) : ℝ)/10^4 ≤ Real.log (primorial (Nat.nth Nat.Prime k) : ℝ) := by
  rw [tao_totient_cert_primorial_nth k]
  have hprod : (∏ i ∈ Finset.range (k+1), Nat.nth Nat.Prime i)
      = ∏ i ∈ Finset.range (k+1), ptab i :=
    Finset.prod_congr rfl (fun i hi => by
      rw [Finset.mem_range] at hi
      exact tao_totient_cert_nth_prime_eq i (by omega : i < 66))
  rw [hprod, Nat.cast_prod]
  rw [Real.log_prod (fun i hi => by
    rw [Finset.mem_range] at hi
    have hp : 0 < ptab i := by
      rw [← tao_totient_cert_nth_prime_eq i (by omega : i < 66)]
      exact (Nat.prime_nth_prime i).pos
    exact_mod_cast hp.ne')]
  simp only [Snum]
  rw [Nat.cast_sum]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 10^4)]
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mem_range] at hi
  exact theta_cert_clbZ_le_log (ptab i) (tao_totient_cert_ptab_mem i (by omega : i < 66))

lemma t3_primorial_65 : primorial (Nat.nth Nat.Prime 65) = Pnum 66 := by
  rw [tao_totient_cert_primorial_nth 65]
  rw [show (∏ i ∈ Finset.range (65+1), Nat.nth Nat.Prime i)
      = ∏ i ∈ Finset.range (65+1), ptab i from
    Finset.prod_congr rfl (fun i hi => by
      rw [Finset.mem_range] at hi
      exact tao_totient_cert_nth_prime_eq i (by omega : i < 66))]
  decide

lemma t3_exp294 : Real.exp 294 < (Pnum 66 : ℝ) := by
  have hlog : (294:ℝ) < Real.log (Pnum 66 : ℝ) := by
    have hSl := Snum_le_log 65 (by norm_num)
    rw [t3_primorial_65] at hSl
    have hnum : (294:ℝ) < (Snum 66 : ℝ)/10^4 := by
      have h : 2940000 < Snum 66 := by decide
      have h' : (2940000:ℝ) < (Snum 66 : ℝ) := by exact_mod_cast h
      rw [lt_div_iff₀ (by norm_num : (0:ℝ) < 10^4)]
      linarith
    linarith
  calc Real.exp 294 < Real.exp (Real.log (Pnum 66 : ℝ)) := Real.exp_lt_exp.mpr hlog
    _ = (Pnum 66 : ℝ) := Real.exp_log (by exact_mod_cast (by decide : 0 < Pnum 66))

lemma t3_exp_gamma_ge : (178107237/10^8 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant := by
  calc (178107237/10^8 : ℝ)
      ≤ ∑ i ∈ Finset.range 12, (57721565/10^8:ℝ)^i / (i.factorial : ℝ) := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp (57721565/10^8) := Real.sum_le_exp_of_nonneg (by norm_num) 12
    _ ≤ Real.exp Real.eulerMascheroniConstant := Real.exp_le_exp.mpr theta_cert_totient_gamma_lower

lemma t3_mono (A c s t : ℝ) (hA : 0 < A) (hc : 0 < c)
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

lemma t3_amgm (A c t : ℝ) (hA : 0 < A) (hc : 0 < c) (ht : 0 < t) :
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

/-- Finite verification of the Rosser--Schoenfeld totient bound. -/
theorem solution (n : ℕ) (hn : 3 ≤ n)
    (hfin : (n : ℝ) < Real.exp 294) :
    ∃ m : ℕ, 1 ≤ m ∧ (n : ℝ) < Real.exp (Chebyshev.theta (Nat.nth Nat.Prime m)) ∧
      (∏ i ∈ Finset.range m,
        (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1)) <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
          2.50637 / Real.log (Real.log (n : ℝ)) := by
  have hex : ∃ j, n < primorial (Nat.nth Nat.Prime j) :=
    ⟨65, by
      rw [t3_primorial_65]
      exact_mod_cast lt_trans hfin t3_exp294⟩
  let m := Nat.find hex
  have hm : n < primorial (Nat.nth Nat.Prime m) := Nat.find_spec hex
  have hmin : ∀ j, j < m → ¬ n < primorial (Nat.nth Nat.Prime j) :=
    fun j hj => Nat.find_min hex hj
  have h1m : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    rw [hm0] at hm
    have hpr2 : primorial (Nat.nth Nat.Prime 0) = 2 := by
      rw [tao_totient_cert_nth_prime_eq 0 (by norm_num)]
      decide
    rw [hpr2] at hm
    omega
  have hm65 : m ≤ 65 := by
    by_contra h
    have h65 : 65 < m := by omega
    have hcon := hmin 65 h65
    rw [t3_primorial_65] at hcon
    have hlt : n < Pnum 66 := by exact_mod_cast lt_trans hfin t3_exp294
    omega
  refine ⟨m, h1m, ?_, ?_⟩
  · have heq : Real.exp (Chebyshev.theta (Nat.nth Nat.Prime m))
        = ((primorial (Nat.nth Nat.Prime m) : ℕ) : ℝ) := by
      rw [Chebyshev.theta_eq_log_primorial]
      rw [Nat.floor_natCast]
      exact Real.exp_log (by exact_mod_cast (primorial_pos _))
    rw [heq]
    exact_mod_cast hm
  · rw [t3_prod_Q_eq_Qpt m h1m hm65]
    set L : ℝ := Real.log (Real.log (n : ℝ)) with hL
    by_cases hm3 : m ≤ 3
    · have hQ : (Qpt m : ℝ) ≤ 15/4 := by interval_cases m <;> norm_num [Qpt, Pnum, Pden]
      have hLpos : 0 < L := by
        rw [hL]
        apply Real.log_pos
        have h3 : (3:ℝ) ≤ n := by exact_mod_cast hn
        have hlog3 : Real.log 3 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) h3
        have h1 : (1:ℝ) < Real.log 3 := by
          rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
          linarith [Real.exp_one_lt_d9]
        linarith
      have hlt : (15/4:ℝ) < 2 * Real.sqrt ((178107237/10^8)*(250637/10^5)) := by
        rw [show (2:ℝ) * Real.sqrt ((178107237/10^8)*(250637/10^5))
            = Real.sqrt (4*((178107237/10^8)*(250637/10^5))) by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
          rw [show Real.sqrt (4:ℝ) = 2 by
            rw [show (4:ℝ) = 2^2 by norm_num]
            exact Real.sqrt_sq (by norm_num)]]
        rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 15/4)]
        norm_num
      calc (Qpt m : ℝ) ≤ 15/4 := hQ
        _ < 2 * Real.sqrt ((178107237/10^8)*(250637/10^5)) := hlt
        _ ≤ (178107237/10^8) * L + (250637/10^5)/L :=
            t3_amgm (178107237/10^8) (250637/10^5) L (by norm_num) (by norm_num) hLpos
        _ ≤ Real.exp Real.eulerMascheroniConstant * L + 2.50637/L := by
            have h1 : (178107237/10^8) * L ≤ Real.exp Real.eulerMascheroniConstant * L :=
              mul_le_mul t3_exp_gamma_ge le_rfl (le_of_lt hLpos)
                (le_trans (by norm_num : (0:ℝ) ≤ 178107237/10^8) t3_exp_gamma_ge)
            have h2 : (250637/10^5)/L = 2.50637/L := by norm_num
            linarith
    · push_neg at hm3
      have hm4 : 4 ≤ m := by omega
      have hT2 := tao_totient_cert_loglog_table (m-1)
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
          (rll m : ℝ) * (178107237/10^8) + (250637/10^5)/(rll m : ℝ) := by
        have h0 := tao_totient_cert_h_check m (Finset.mem_Icc.mpr ⟨hm4, hm65⟩)
        have h0R := (Rat.cast_lt (K := ℝ)).mpr h0
        push_cast at h0R
        exact h0R
      have hmono := t3_mono (Real.exp Real.eulerMascheroniConstant) (2.50637) (rll m) L
        (Real.exp_pos _) (by norm_num) hrllm (le_trans hrllm hLlo) hLlo
        (by
          have hs : (3/2:ℝ) ≤ (rll m:ℝ) := hrllm
          have ht : (3/2:ℝ) ≤ L := le_trans hrllm hLlo
          have hst : (3/2:ℝ)*(3/2) ≤ (rll m:ℝ)*L :=
            mul_le_mul hs ht (by norm_num) (by linarith)
          have h1 : (178107237/10^8) * ((3/2)*(3/2)) ≤
              Real.exp Real.eulerMascheroniConstant * ((rll m)*L) :=
            mul_le_mul t3_exp_gamma_ge hst (by norm_num)
              (le_trans (by norm_num : (0:ℝ) ≤ 178107237/10^8) t3_exp_gamma_ge)
          have h2 : (2.50637:ℝ) ≤ (178107237/10^8) * ((3/2)*(3/2)) := by norm_num
          linarith)
      calc (Qpt m : ℝ) <
            (rll m : ℝ) * (178107237/10^8) + (250637/10^5)/(rll m : ℝ) := hck
        _ ≤ Real.exp Real.eulerMascheroniConstant * (rll m) + 2.50637/(rll m) := by
            have h1 : (rll m : ℝ) * (178107237/10^8)
                ≤ (rll m : ℝ) * Real.exp Real.eulerMascheroniConstant :=
              mul_le_mul_of_nonneg_left t3_exp_gamma_ge (by linarith [hrllm])
            have h2 : (250637/10^5)/(rll m : ℝ) = 2.50637/(rll m : ℝ) := by norm_num
            linarith
        _ ≤ Real.exp Real.eulerMascheroniConstant * L + 2.50637/L := hmono

end TaoFivePrimes

open TaoFivePrimes

/-- Root re-export for the verification harness. -/
theorem solution (n : ℕ) (hn : 3 ≤ n)
    (hfin : (n : ℝ) < Real.exp 294) :
    ∃ m : ℕ, 1 ≤ m ∧ (n : ℝ) < Real.exp (Chebyshev.theta (Nat.nth Nat.Prime m)) ∧
      (∏ i ∈ Finset.range m,
        (Nat.nth Nat.Prime i : ℝ) / ((Nat.nth Nat.Prime i : ℝ) - 1)) <
        Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) +
          2.50637 / Real.log (Real.log (n : ℝ)) :=
  TaoFivePrimes.solution n hn hfin

#print axioms solution
