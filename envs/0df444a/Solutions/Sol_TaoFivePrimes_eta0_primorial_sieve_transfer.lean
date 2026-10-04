-- Prove2me | solution 1 for TaoFivePrimes.eta0_primorial_sieve_transfer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-09T15:26:49.248332+00:00
-- url     : https://prove2.me/submissions/0effebaf-7763-4c9a-af01-2a79c0b6e739

import Definitions.Def_TaoFivePrimes_RepresentationCount
import Definitions.Def_TaoFivePrimes_SmoothedExpSum
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib

open scoped BigOperators ArithmeticFunction.vonMangoldt
open MeasureTheory

namespace TaoFivePrimes

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

/-- The direct Lemma 4.1 transfer needed for the `eta0` weak major arc. -/
theorem eta0_primorial_sieve_transfer
    (x : ℕ) (h1 : 87 * 10 ^ 35 ≤ x) (theta : ℝ) :
    let y : ℝ := (x : ℝ) / 1000
    ‖smoothedExpSum eta0 (primorial (Nat.sqrt (x / 1000))) y theta -
        smoothedExpSum eta0 1 y theta‖ ≤
      (9 : ℝ) / 10 ^ 8 * y := by
  dsimp only
  let y : ℝ := (x : ℝ) / 1000
  let N : ℕ := x / 1000
  let M : ℕ := Nat.sqrt N
  let q : ℕ := primorial M
  let term : ℕ → ℂ := fun n =>
    (Λ n : ℂ) * expCircle (theta * n) * (eta0 ((n : ℝ) / y) : ℂ)
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) h1
  have hypos : 0 < y := by dsimp [y]; positivity
  have hfloor : ⌊y⌋₊ = N := by
    dsimp [y, N]
    convert Nat.floor_div_natCast (x : ℝ) 1000 using 1 <;> simp
  have htail (n : ℕ) (hn : n ∉ Finset.range (N + 1)) :
      eta0 ((n : ℝ) / y) = 0 := by
    rw [Finset.mem_range, not_lt] at hn
    have hfloorlt : ⌊y⌋₊ < n := by omega
    have hylt : y < n := Nat.lt_of_floor_lt hfloorlt
    apply eta0_eq_zero_of_ge_st
    apply (le_div_iff₀ hypos).2
    simpa using (show y ≤ (n : ℝ) by exact_mod_cast hylt.le)
  have hq : smoothedExpSum eta0 q y theta =
      ∑ n ∈ Finset.range (N + 1),
        if n.Coprime q then term n else 0 := by
    unfold smoothedExpSum
    rw [tsum_eq_sum (s := Finset.range (N + 1)) (fun n hn => by
      rw [htail n hn]
      simp)]
  have hone : smoothedExpSum eta0 1 y theta =
      ∑ n ∈ Finset.range (N + 1), term n := by
    unfold smoothedExpSum
    rw [tsum_eq_sum (s := Finset.range (N + 1)) (fun n hn => by
      rw [htail n hn]
      simp)]
    simp [term]
  change ‖smoothedExpSum eta0 q y theta - smoothedExpSum eta0 1 y theta‖ ≤ _
  rw [hq, hone, ← Finset.sum_sub_distrib]
  have hnorm :
      ‖∑ n ∈ Finset.range (N + 1),
          ((if n.Coprime q then term n else 0) - term n)‖ ≤
        3 * ∑ n ∈ (Finset.range (N + 1)).filter (fun n => ¬ n.Coprime q), Λ n := by
    calc
      ‖∑ n ∈ Finset.range (N + 1),
          ((if n.Coprime q then term n else 0) - term n)‖ ≤
          ∑ n ∈ Finset.range (N + 1),
            ‖(if n.Coprime q then term n else 0) - term n‖ :=
        norm_sum_le _ _
      _ ≤ ∑ n ∈ Finset.range (N + 1),
          if ¬ n.Coprime q then 3 * Λ n else 0 := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hc : n.Coprime q
        · rw [if_pos hc, if_neg (by simpa using hc)]
          simp
        · simp only [hc, if_false, not_false_eq_true, if_true, zero_sub, norm_neg]
          simp only [term, norm_mul, Complex.norm_real, expCircle_norm_st,
            Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
            abs_of_nonneg (eta0_nonneg_st _), mul_one]
          simpa [mul_comm] using
            (mul_le_mul_of_nonneg_left (eta0_le_three_st _)
              ArithmeticFunction.vonMangoldt_nonneg)
      _ = 3 * ∑ n ∈ (Finset.range (N + 1)).filter (fun n => ¬ n.Coprime q), Λ n := by
        rw [Finset.mul_sum]
        simp only [Finset.sum_filter]
  let bad : Finset ℕ :=
    (Finset.range (N + 1)).filter (fun n => ¬ n.Coprime q)
  have hprime :
      ∑ n ∈ bad.filter Nat.Prime, Λ n ≤ Chebyshev.theta (M : ℝ) := by
    calc
      ∑ n ∈ bad.filter Nat.Prime, Λ n =
          ∑ n ∈ bad.filter Nat.Prime, Real.log n := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [Finset.mem_filter] at hn
        exact ArithmeticFunction.vonMangoldt_apply_prime hn.2
      _ ≤ ∑ n ∈ M.primesLE, Real.log n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Finset.mem_filter] at hn
          rcases hn with ⟨hnbad, hp⟩
          rw [Nat.mem_primesLE]
          refine ⟨?_, hp⟩
          have hnq : ¬ n.Coprime q := (Finset.mem_filter.mp hnbad).2
          have hdvd : n ∣ q := by
            by_contra hndvd
            exact hnq ((hp.coprime_iff_not_dvd).2 hndvd)
          dsimp [q] at hdvd
          exact (hp.dvd_primorial_iff).1 hdvd
        · intro n hn hnot
          have hp : n.Prime := (Nat.mem_primesLE.mp hn).2
          exact Real.log_nonneg (by exact_mod_cast hp.one_le)
      _ = Chebyshev.theta (M : ℝ) :=
        (Chebyshev.theta_eq_sum_primesLE_log M).symm
  have hcomp :
      ∑ n ∈ bad.filter (fun n => ¬ n.Prime), Λ n ≤
        Chebyshev.psi y - Chebyshev.theta y := by
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
        Chebyshev.theta (M : ℝ) +
          (Chebyshev.psi y - Chebyshev.theta y) := by
    rw [← Finset.sum_filter_add_sum_filter_not bad Nat.Prime (fun n => Λ n)]
    exact add_le_add hprime hcomp
  have hy_lower : (87 * 10 ^ 32 : ℝ) ≤ y := by
    have hxreal : (87 * 10 ^ 35 : ℝ) ≤ (x : ℝ) := by exact_mod_cast h1
    dsimp [y]
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000)).2
    norm_num at hxreal ⊢
    exact hxreal
  have hyone : (1 : ℝ) ≤ y := by
    norm_num at hy_lower ⊢
    linarith
  have hNle : (N : ℝ) ≤ y := by
    rw [← hfloor]
    exact Nat.floor_le hypos.le
  have hMsq_nat : M * M ≤ N := by
    simpa [M] using Nat.sqrt_le N
  have hMsq : (M : ℝ) ^ 2 ≤ y := by
    calc
      (M : ℝ) ^ 2 = (M * M : ℕ) := by simp [pow_two]
      _ ≤ (N : ℝ) := by exact_mod_cast hMsq_nat
      _ ≤ y := hNle
  have hMle : (M : ℝ) ≤ √y := by
    exact (Real.le_sqrt (by positivity) hypos.le).2 hMsq
  have htheta : Chebyshev.theta (M : ℝ) ≤ 3 * √y := by
    calc
      Chebyshev.theta (M : ℝ) ≤ Real.log 4 * (M : ℝ) :=
        Chebyshev.theta_le_log4_mul_x (by positivity)
      _ ≤ 3 * (M : ℝ) := by
        gcongr
        have hl := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
        norm_num at hl ⊢
        exact hl
      _ ≤ 3 * √y := by gcongr
  have hlog : Real.log y ≤ 4 * y ^ (1 / 4 : ℝ) := by
    have h := Real.log_le_rpow_div hypos.le (by norm_num : (0 : ℝ) < 1 / 4)
    convert h using 1 <;> ring
  have hpsi :
      Chebyshev.psi y - Chebyshev.theta y ≤ 8 * y ^ (3 / 4 : ℝ) := by
    calc
      Chebyshev.psi y - Chebyshev.theta y ≤ 2 * √y * Real.log y :=
        Chebyshev.psi_sub_theta_le hyone
      _ ≤ 2 * √y * (4 * y ^ (1 / 4 : ℝ)) := by
        gcongr
      _ = 8 * y ^ (3 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        calc
          2 * y ^ (1 / 2 : ℝ) * (4 * y ^ (1 / 4 : ℝ)) =
              8 * (y ^ (1 / 2 : ℝ) * y ^ (1 / 4 : ℝ)) := by ring
          _ = 8 * y ^ (3 / 4 : ℝ) := by
            rw [← Real.rpow_add hypos]
            norm_num
  have hanalytic :
      ‖∑ n ∈ Finset.range (N + 1),
          ((if n.Coprime q then term n else 0) - term n)‖ ≤
        9 * √y + 24 * y ^ (3 / 4 : ℝ) := by
    calc
      ‖∑ n ∈ Finset.range (N + 1),
          ((if n.Coprime q then term n else 0) - term n)‖ ≤
          3 * ∑ n ∈ bad, Λ n := by simpa [bad] using hnorm
      _ ≤ 3 * (Chebyshev.theta (M : ℝ) +
          (Chebyshev.psi y - Chebyshev.theta y)) := by gcongr
      _ ≤ 9 * √y + 24 * y ^ (3 / 4 : ℝ) := by nlinarith
  have hbase : ((3 * 10 ^ 8 : ℝ) ^ (4 : ℕ)) ≤ y := by
    norm_num at hy_lower ⊢
    linarith
  have hquarter : (3 * 10 ^ 8 : ℝ) ≤ y ^ (1 / 4 : ℝ) := by
    have hr := Real.rpow_le_rpow
      (show (0 : ℝ) ≤ (3 * 10 ^ 8 : ℝ) ^ (4 : ℕ) by positivity)
      hbase (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    have hroot :
        (((3 * 10 ^ 8 : ℝ) ^ (4 : ℕ)) ^ (1 / 4 : ℝ)) =
          (3 * 10 ^ 8 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hroot] at hr
    exact hr
  have hquarter_nine : (9 : ℝ) ≤ y ^ (1 / 4 : ℝ) := by
    norm_num at hquarter ⊢
    linarith
  have hsqrt_small : 9 * √y ≤ y ^ (3 / 4 : ℝ) := by
    calc
      9 * √y = √y * 9 := by ring
      _ ≤ √y * y ^ (1 / 4 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hquarter_nine (Real.sqrt_nonneg y)
      _ = y ^ (3 / 4 : ℝ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hypos]
        norm_num
  have hquarter_nonneg : 0 ≤ y ^ (1 / 4 : ℝ) := Real.rpow_nonneg hypos.le _
  have hthreequarter_nonneg : 0 ≤ y ^ (3 / 4 : ℝ) := Real.rpow_nonneg hypos.le _
  have hy_factor : y = y ^ (3 / 4 : ℝ) * y ^ (1 / 4 : ℝ) := by
    calc
      y = y ^ (1 : ℝ) := (Real.rpow_one y).symm
      _ = y ^ ((3 / 4 : ℝ) + (1 / 4 : ℝ)) := by norm_num
      _ = y ^ (3 / 4 : ℝ) * y ^ (1 / 4 : ℝ) := Real.rpow_add hypos _ _
  have hcoeff : (25 : ℝ) ≤ (9 / 10 ^ 8 : ℝ) * y ^ (1 / 4 : ℝ) := by
    norm_num at hquarter ⊢
    nlinarith
  calc
    ‖∑ n ∈ Finset.range (N + 1),
        ((if n.Coprime q then term n else 0) - term n)‖ ≤
        9 * √y + 24 * y ^ (3 / 4 : ℝ) := hanalytic
    _ ≤ 25 * y ^ (3 / 4 : ℝ) := by nlinarith
    _ ≤ ((9 / 10 ^ 8 : ℝ) * y ^ (1 / 4 : ℝ)) *
        y ^ (3 / 4 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hcoeff hthreequarter_nonneg
    _ = (9 : ℝ) / 10 ^ 8 *
        (y ^ (3 / 4 : ℝ) * y ^ (1 / 4 : ℝ)) := by ring
    _ = (9 : ℝ) / 10 ^ 8 * y := by rw [← hy_factor]

end TaoFivePrimes

open TaoFivePrimes

theorem solution
    (x : ℕ) (h1 : 87 * 10 ^ 35 ≤ x) (theta : ℝ) :
    let y : ℝ := (x : ℝ) / 1000
    ‖smoothedExpSum eta0 (primorial (Nat.sqrt (x / 1000))) y theta -
        smoothedExpSum eta0 1 y theta‖ ≤
      (9 : ℝ) / 10 ^ 8 * y := by
  exact TaoFivePrimes.eta0_primorial_sieve_transfer x h1 theta

#print axioms solution
