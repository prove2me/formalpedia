-- Prove2me | solution 1 for TaoFivePrimes.small_q_modulus_transfer_source_envelope
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-09-12T13:43:15.463592+00:00
-- url     : https://prove2.me/submissions/26fa51c0-287c-4b4b-a6b8-3ac048574313

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace TaoFivePrimes

-- Cutoff/truncation arguments adapted from accepted submission
-- 0effebaf-7763-4c9a-af01-2a79c0b6e739 by marwahaha.
private lemma eta0_nonneg_st (t : ℝ) : 0 ≤ eta0 t := by
  unfold eta0
  split_ifs <;> positivity

private lemma eta0_le_three_st (t : ℝ) : eta0 t ≤ 3 := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold eta0
  split_ifs
  · have hm : max 0 (Real.log 2 - |Real.log (2 * t)|) ≤ Real.log 2 :=
      max_le hl (by linarith [abs_nonneg (Real.log (2 * t))])
    nlinarith [Real.log_two_lt_d9]
  · norm_num

private lemma eta0_eq_zero_of_ge_st {t : ℝ} (ht : 1 ≤ t) : eta0 t = 0 := by
  unfold eta0
  rw [if_pos (by linarith)]
  have hlog : Real.log 2 ≤ Real.log (2 * t) := by
    exact Real.log_le_log (by norm_num) (by linarith)
  have hcut : Real.log 2 - |Real.log (2 * t)| ≤ 0 :=
    sub_nonpos.mpr (hlog.trans (le_abs_self (Real.log (2 * t))))
  rw [max_eq_left hcut, mul_zero]

private lemma expCircle_norm_st (a : ℝ) : ‖expCircle a‖ = 1 := by
  unfold expCircle
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ)) =
      ((2 * Real.pi * a : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _


lemma coprime_indicator_difference_bound (n q r : ℕ) (z : ℂ) :
    ‖(if n.Coprime q then z else 0) - (if n.Coprime r then z else 0)‖ ≤
      if ¬ n.Coprime (q * r) then ‖z‖ else 0 := by
  by_cases hq : n.Coprime q
  · by_cases hr : n.Coprime r
    · rw [if_pos hq, if_pos hr, sub_self, norm_zero]
      positivity
    · rw [if_pos hq, if_neg hr, sub_zero]
      have hbad : ¬ n.Coprime (q * r) := by
        intro h
        exact hr (Nat.coprime_mul_iff_right.mp h).2
      rw [if_pos hbad]
  · by_cases hr : n.Coprime r
    · rw [if_neg hq, if_pos hr, zero_sub, norm_neg]
      have hbad : ¬ n.Coprime (q * r) := by
        intro h
        exact hq (Nat.coprime_mul_iff_right.mp h).1
      rw [if_pos hbad]
    · rw [if_neg hq, if_neg hr, sub_self, norm_zero]
      positivity

lemma eta0_transfer_bad_mass
    (x alpha : ℝ) (q0 : ℕ) (hx : 10 ^ 20 ≤ x)
    (hq0pos : 0 < q0)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x) :
    ‖smoothedExpSum eta0 q0 x alpha - smoothedExpSum eta0 2 x alpha‖ ≤
      3 * (Chebyshev.theta (Real.sqrt x) + (Chebyshev.psi x - Chebyshev.theta x)) := by
  let N : ℕ := ⌊x⌋₊
  let M : ℕ := ⌊Real.sqrt x⌋₊
  let q : ℕ := q0 * 2
  let term : ℕ → ℂ := fun n =>
    (Λ n : ℂ) * expCircle (alpha * n) * (eta0 ((n : ℝ) / x) : ℂ)
  have hxpos : 0 < x := by linarith
  have hfloor : ⌊x⌋₊ = N := rfl
  have htail (n : ℕ) (hn : n ∉ Finset.range (N + 1)) :
      eta0 ((n : ℝ) / x) = 0 := by
    rw [Finset.mem_range, not_lt] at hn
    have hfloorlt : ⌊x⌋₊ < n := by omega
    have hxlt : x < n := Nat.lt_of_floor_lt hfloorlt
    apply eta0_eq_zero_of_ge_st
    apply (le_div_iff₀ hxpos).2
    simpa using hxlt.le
  have hfinite (m : ℕ) : smoothedExpSum eta0 m x alpha =
      ∑ n ∈ Finset.range (N + 1), if n.Coprime m then term n else 0 := by
    unfold smoothedExpSum
    rw [tsum_eq_sum (s := Finset.range (N + 1)) (fun n hn => by rw [htail n hn]; simp)]
  rw [hfinite q0, hfinite 2, ← Finset.sum_sub_distrib]
  have hterm (n : ℕ) : ‖term n‖ ≤ 3 * Λ n := by
    simp only [term, norm_mul, Complex.norm_real, expCircle_norm_st,
      Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      abs_of_nonneg (eta0_nonneg_st _), mul_one]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (eta0_le_three_st _)
      ArithmeticFunction.vonMangoldt_nonneg
  let bad : Finset ℕ := (Finset.range (N + 1)).filter (fun n => ¬ n.Coprime q)
  have hnorm :
      ‖∑ n ∈ Finset.range (N + 1),
        ((if n.Coprime q0 then term n else 0) - (if n.Coprime 2 then term n else 0))‖ ≤
      3 * ∑ n ∈ bad, Λ n := by
    calc
      _ ≤ ∑ n ∈ Finset.range (N + 1),
          ‖(if n.Coprime q0 then term n else 0) - (if n.Coprime 2 then term n else 0)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range (N + 1), if ¬ n.Coprime q then 3 * Λ n else 0 := by
        apply Finset.sum_le_sum
        intro n hn
        have hi := coprime_indicator_difference_bound n q0 2 (term n)
        change _ ≤ if ¬ n.Coprime q then ‖term n‖ else 0 at hi
        by_cases hc : ¬ n.Coprime q
        · rw [if_pos hc] at hi ⊢
          exact hi.trans (hterm n)
        · rw [if_neg hc] at hi ⊢
          exact hi
      _ = 3 * ∑ n ∈ bad, Λ n := by
        rw [Finset.mul_sum]
        simp only [bad, Finset.sum_filter]
  have hprime : ∑ n ∈ bad.filter Nat.Prime, Λ n ≤ Chebyshev.theta (Real.sqrt x) := by
    calc
      _ = ∑ n ∈ bad.filter Nat.Prime, Real.log n := by
        apply Finset.sum_congr rfl
        intro n hn
        exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hn).2
      _ ≤ ∑ n ∈ M.primesLE, Real.log n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          obtain ⟨hnbad, hp⟩ := Finset.mem_filter.mp hn
          rw [Nat.mem_primesLE]
          refine ⟨?_, hp⟩
          have hnq : ¬ n.Coprime q := (Finset.mem_filter.mp hnbad).2
          have hdvd : n ∣ q := by
            by_contra hndvd
            exact hnq ((hp.coprime_iff_not_dvd).2 hndvd)
          have hr : (n : ℝ) ≤ Real.sqrt x := by
            rcases hp.dvd_mul.mp hdvd with hd | hd
            · exact hq0 n (hp.mem_primeFactors hd (Nat.ne_of_gt hq0pos))
            · have hnle : n ≤ 2 := Nat.le_of_dvd (by norm_num) hd
              have hs : (2 : ℝ) ≤ Real.sqrt x := by
                apply (Real.le_sqrt (by norm_num) hxpos.le).2
                norm_num
                linarith
              exact le_trans (by exact_mod_cast hnle) hs
          exact Nat.le_floor hr
        · intro n hn hnot
          exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hn).2.one_le)
      _ = Chebyshev.theta (M : ℝ) := (Chebyshev.theta_eq_sum_primesLE_log M).symm
      _ ≤ Chebyshev.theta (Real.sqrt x) := Chebyshev.theta_mono (Nat.floor_le (Real.sqrt_nonneg x))
  have hcomp :
      ∑ n ∈ bad.filter (fun n => ¬ n.Prime), Λ n ≤
        Chebyshev.psi x - Chebyshev.theta x := by
    let comp : Finset ℕ := bad.filter (fun n => ¬ n.Prime)
    have herase :
        ∑ n ∈ comp, Λ n = ∑ n ∈ comp.erase 0, Λ n := by
      by_cases hzero : 0 ∈ comp
      · calc
          ∑ n ∈ comp, Λ n = (∑ n ∈ comp.erase 0, Λ n) + Λ 0 :=
            (comp.sum_erase_add (fun n => Λ n) hzero).symm
          _ = ∑ n ∈ comp.erase 0, Λ n := by simp
      · simp [hzero]
    rw [show bad.filter (fun n => ¬ n.Prime) = comp by rfl, herase,
      Chebyshev.psi_sub_theta_eq_sum_not_prime]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [Finset.mem_erase, Finset.mem_filter] at hn
      rcases hn with ⟨hnzero, hncomp, hnprime⟩
      rw [Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨?_, ?_⟩, hnprime⟩
      · omega
      · have hnrange : n ∈ Finset.range (N + 1) := by
          exact (Finset.mem_filter.mp hncomp).1
        rw [hfloor]
        simpa [Finset.mem_range] using hnrange
    · intro n hn hnot
      exact ArithmeticFunction.vonMangoldt_nonneg
  have hbad :
      ∑ n ∈ bad, Λ n ≤
        Chebyshev.theta (Real.sqrt x) +
          (Chebyshev.psi x - Chebyshev.theta x) := by
    rw [← Finset.sum_filter_add_sum_filter_not bad Nat.Prime (fun n => Λ n)]
    exact add_le_add hprime hcomp
  exact hnorm.trans (mul_le_mul_of_nonneg_left hbad (by norm_num))

end TaoFivePrimes

namespace TaoFivePrimes

lemma log_four_le_two_transfer : Real.log 4 ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have he : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  linarith

lemma psi_le_six_transfer (z : ℝ) (hz : 0 ≤ z) : Chebyshev.psi z ≤ 6 * z := by
  have h := Chebyshev.psi_le_const_mul_self hz
  have hc : (Real.log 4 + 4) * z ≤ 6 * z := by
    gcongr
    linarith [log_four_le_two_transfer]
  exact h.trans hc

lemma psi_le_three_large_transfer (z : ℝ) (hz : 4096 ≤ z) :
    Chebyshev.psi z ≤ 3 * z := by
  have hz0 : 0 < z := by linarith
  have hroot : (8 : ℝ) ≤ z ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (8 : ℝ) ^ (4 : ℕ))
      (show (8 : ℝ) ^ (4 : ℕ) ≤ z by norm_num; linarith) (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
    norm_num at h
    exact h
  have hlog : Real.log z ≤ 4 * z ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div hz0.le (by norm_num : (0 : ℝ) < 1 / 4)
    convert h using 1 <;> ring
  have hmain : Real.log 4 * z ≤ 2 * z :=
    mul_le_mul_of_nonneg_right log_four_le_two_transfer hz0.le
  have herr : 2 * Real.sqrt z * Real.log z ≤ z := by
    calc
      _ ≤ 2 * Real.sqrt z * (4 * z ^ (1 / 4 : ℝ)) := by gcongr
      _ = 8 * z ^ (3 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        rw [show (3 / 4 : ℝ) = 1 / 2 + 1 / 4 by norm_num, Real.rpow_add hz0]
        ring
      _ ≤ z ^ (1 / 4 : ℝ) * z ^ (3 / 4 : ℝ) := by gcongr
      _ = z := by rw [← Real.rpow_add hz0]; norm_num
  have h := Chebyshev.psi_le (show 1 ≤ z by linarith)
  linarith

lemma psi_sub_theta_le_four_sqrt_transfer (x : ℝ) (hx : 10 ^ 20 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 4 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hs : (4096 : ℝ) ≤ Real.sqrt x := by
    apply (Real.le_sqrt (by norm_num) hx0.le).2
    norm_num
    linarith
  have hroot : (12 : ℝ) ≤ x ^ (1 / 6 : ℝ) := by
    have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (12 : ℝ) ^ (6 : ℕ))
      (show (12 : ℝ) ^ (6 : ℕ) ≤ x by norm_num; linarith) (by norm_num : (0 : ℝ) ≤ 1 / 6)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)] at h
    norm_num at h
    exact h
  have hsmall : 12 * x ^ (1 / 3 : ℝ) ≤ Real.sqrt x := by
    calc
      _ ≤ x ^ (1 / 6 : ℝ) * x ^ (1 / 3 : ℝ) := by gcongr
      _ = Real.sqrt x := by rw [← Real.rpow_add hx0, Real.sqrt_eq_rpow]; norm_num
  have horder : x ^ (1 / 5 : ℝ) ≤ x ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have h2 := psi_le_three_large_transfer (Real.sqrt x) hs
  have h3 := psi_le_six_transfer (x ^ (1 / 3 : ℝ)) (by positivity)
  have h5 := psi_le_six_transfer (x ^ (1 / 5 : ℝ)) (by positivity)
  rw [Real.sqrt_eq_rpow] at h2
  simp only [one_div] at h2 h3 h5 hsmall horder
  rw [Real.sqrt_eq_rpow] at hsmall ⊢
  norm_num at h h2 h3 h5 hsmall horder ⊢
  linarith

end TaoFivePrimes

open TaoFivePrimes

theorem solution
    (x alpha : ℝ) (q0 : ℕ)
    (hx : (10 : ℝ) ^ 20 ≤ x)
    (hq0pos : 0 < q0)
    (hq0 : ∀ p ∈ q0.primeFactors, (p : ℝ) ≤ Real.sqrt x) :
    ‖smoothedExpSum eta0 q0 x alpha - smoothedExpSum eta0 2 x alpha‖ ≤
      20.16 * Real.sqrt x := by
  have ht := eta0_transfer_bad_mass x alpha q0 hx hq0pos hq0
  have hp := psi_sub_theta_le_four_sqrt_transfer x hx
  have htheta := Chebyshev.theta_le_log4_mul_x (Real.sqrt_nonneg x)
  have htheta2 : Chebyshev.theta (Real.sqrt x) ≤ 2 * Real.sqrt x :=
    htheta.trans (mul_le_mul_of_nonneg_right log_four_le_two_transfer (Real.sqrt_nonneg x))
  nlinarith [Real.sqrt_nonneg x]


