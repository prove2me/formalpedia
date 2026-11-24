-- Prove2me | solution 1 for PrimePairSieve.sieve_constants_certificate
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-23T14:49:13.061934+00:00
-- url     : https://prove2.me/submissions/91b4ca4a-771c-4be3-88cd-952059ec7610

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Log
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries

open scoped BigOperators

set_option maxHeartbeats 1000000

/-! ## Auxiliary rational certificate for `log p`

For a natural number `p ≥ 1` with `2^k ≤ p`, we lower bound `Real.log p` by the
rational quantity `cval p k`: `k · 0.6931471803` (a certified lower bound for
`k log 2`) plus the first six terms of the Taylor expansion of `-log (1-v)`,
where `v = (p - 2^k)/p`. -/

private def cval (p k : ℕ) : ℚ :=
  (k : ℚ) * (6931471803 / 10 ^ 10) +
    ∑ n ∈ Finset.range 6, (((p - 2 ^ k : ℕ) : ℚ) / (p : ℚ)) ^ (n + 1) / ((n : ℚ) + 1)

private lemma log_ge_interval (p k : ℕ) (hp : 0 < p) (hlo : 2 ^ k ≤ p) :
    (k : ℝ) * (0.6931471803 : ℝ) +
        ∑ n ∈ Finset.range 6, (((p - 2 ^ k : ℕ) : ℝ) / (p : ℝ)) ^ (n + 1) / ((n : ℝ) + 1)
      ≤ Real.log p := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have h2k : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hle : (2 : ℝ) ^ k ≤ (p : ℝ) := by exact_mod_cast hlo
  have hcast_sub : ((p - 2 ^ k : ℕ) : ℝ) = (p : ℝ) - (2 : ℝ) ^ k := by
    rw [Nat.cast_sub hlo]; push_cast; ring
  have hv0 : (0 : ℝ) ≤ ((p - 2 ^ k : ℕ) : ℝ) / (p : ℝ) := by positivity
  have hv1 : ((p - 2 ^ k : ℕ) : ℝ) / (p : ℝ) < 1 := by
    rw [div_lt_one hpR, hcast_sub]
    linarith
  have hs := Real.hasSum_pow_div_log_of_abs_lt_one
    (x := ((p - 2 ^ k : ℕ) : ℝ) / (p : ℝ)) (by rw [abs_of_nonneg hv0]; exact hv1)
  have hpart : ∑ n ∈ Finset.range 6,
        (((p - 2 ^ k : ℕ) : ℝ) / (p : ℝ)) ^ (n + 1) / ((n : ℝ) + 1)
      ≤ -Real.log (1 - ((p - 2 ^ k : ℕ) : ℝ) / (p : ℝ)) := by
    have h := hs.summable.sum_le_tsum (Finset.range 6) (fun n _ => by positivity)
    rwa [hs.tsum_eq] at h
  have hlog : Real.log p =
      (k : ℝ) * Real.log 2 + (-Real.log (1 - ((p - 2 ^ k : ℕ) : ℝ) / (p : ℝ))) := by
    have h1v : 1 - ((p - 2 ^ k : ℕ) : ℝ) / (p : ℝ) = (2 : ℝ) ^ k / (p : ℝ) := by
      rw [hcast_sub]
      field_simp
      ring
    rw [h1v, Real.log_div (by positivity) (by positivity), Real.log_pow]
    ring
  calc (k : ℝ) * (0.6931471803 : ℝ) +
        ∑ n ∈ Finset.range 6, (((p - 2 ^ k : ℕ) : ℝ) / (p : ℝ)) ^ (n + 1) / ((n : ℝ) + 1)
      ≤ (k : ℝ) * Real.log 2 + (-Real.log (1 - ((p - 2 ^ k : ℕ) : ℝ) / (p : ℝ))) := by
        have h2 : (0.6931471803 : ℝ) ≤ Real.log 2 := Real.log_two_gt_d9.le
        have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith [mul_le_mul_of_nonneg_left h2 hk, hpart]
    _ = Real.log p := hlog.symm

private lemma cval_le_log (p : ℕ) (hp : 0 < p) : ((cval p p.log2 : ℚ) : ℝ) ≤ Real.log p := by
  have hcast : ((cval p p.log2 : ℚ) : ℝ) =
      (p.log2 : ℝ) * (0.6931471803 : ℝ) +
        ∑ n ∈ Finset.range 6, (((p - 2 ^ p.log2 : ℕ) : ℝ) / (p : ℝ)) ^ (n + 1) /
          ((n : ℝ) + 1) := by
    simp only [cval]
    push_cast
    norm_num
  rw [hcast]
  exact log_ge_interval p p.log2 hp (Nat.log2_self_le hp.ne')

/-! ## Monotonicity and explicit bounds for the twin-prime partial products -/

private lemma twinPartial_fac_nonneg (p : ℕ) :
    (0 : ℝ) ≤ (if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) := by
  split_ifs with h
  · have h3 : (3 : ℝ) ≤ (p : ℝ) := by
      have : 3 ≤ p := by omega
      exact_mod_cast this
    have hden : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have hle : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by nlinarith)]
      exact hden
    linarith
  · norm_num

private lemma twinPartial_fac_le_one (p : ℕ) :
    (if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1) ≤ 1 := by
  split_ifs with h
  · have hpos : (0 : ℝ) ≤ 1 / ((p : ℝ) - 1) ^ 2 := div_nonneg zero_le_one (sq_nonneg _)
    linarith
  · norm_num

private lemma twinPartial_nonneg (Q : ℕ) : (0 : ℝ) ≤ TaoFivePrimes.twinPrimePartial Q := by
  rw [TaoFivePrimes.twinPrimePartial]
  exact Finset.prod_nonneg (fun p _ => twinPartial_fac_nonneg p)

private lemma cast_prod81 :
    ((∏ p ∈ Finset.range 81,
        (if Nat.Prime p ∧ 2 < p then (1 : ℚ) - 1 / ((p : ℚ) - 1) ^ 2 else 1) : ℚ) : ℝ)
      = ∏ p ∈ Finset.range 81,
        (if Nat.Prime p ∧ 2 < p then (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 else 1) := by
  rw [Rat.cast_prod]
  apply Finset.prod_congr rfl
  intro p _
  rw [apply_ite (Rat.cast : ℚ → ℝ)]
  split_ifs <;> push_cast <;> norm_num

private lemma cast_prod201 :
    ((∏ p ∈ Finset.range 201,
        (if Nat.Prime p ∧ 2 < p then (1 : ℚ) - 1 / ((p : ℚ) - 1) ^ 2 else 1) : ℚ) : ℝ)
      = ∏ p ∈ Finset.range 201,
        (if Nat.Prime p ∧ 2 < p then (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 else 1) := by
  rw [Rat.cast_prod]
  apply Finset.prod_congr rfl
  intro p _
  rw [apply_ite (Rat.cast : ℚ → ℝ)]
  split_ifs <;> push_cast <;> norm_num

private lemma twinPartial_80_ge : (0.6534 : ℝ) ≤ TaoFivePrimes.twinPrimePartial 80 := by
  have hQ : (6534 / 10000 : ℚ) ≤
      ∏ p ∈ Finset.range 81,
        (if Nat.Prime p ∧ 2 < p then (1 : ℚ) - 1 / ((p : ℚ) - 1) ^ 2 else 1) := by
    decide +kernel
  have hR : ((6534 / 10000 : ℚ) : ℝ) ≤
      ∏ p ∈ Finset.range 81,
        (if Nat.Prime p ∧ 2 < p then (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 else 1) := by
    have h2 : ((6534 / 10000 : ℚ) : ℝ) ≤
        ((∏ p ∈ Finset.range 81,
          (if Nat.Prime p ∧ 2 < p then (1 : ℚ) - 1 / ((p : ℚ) - 1) ^ 2 else 1) : ℚ) : ℝ) :=
      Rat.cast_le.mpr hQ
    rwa [cast_prod81] at h2
  have hnum : ((6534 / 10000 : ℚ) : ℝ) = (0.6534 : ℝ) := by norm_num
  rw [hnum] at hR
  simpa [TaoFivePrimes.twinPrimePartial] using hR

private lemma twinPartial_200_le : TaoFivePrimes.twinPrimePartial 200 ≤ (0.6607 : ℝ) := by
  have hQ : (∏ p ∈ Finset.range 201,
        (if Nat.Prime p ∧ 2 < p then (1 : ℚ) - 1 / ((p : ℚ) - 1) ^ 2 else 1)) ≤
      (6607 / 10000 : ℚ) := by
    decide +kernel
  have hR : (∏ p ∈ Finset.range 201,
        (if Nat.Prime p ∧ 2 < p then (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 else 1)) ≤
      ((6607 / 10000 : ℚ) : ℝ) := by
    have h2 : ((∏ p ∈ Finset.range 201,
          (if Nat.Prime p ∧ 2 < p then (1 : ℚ) - 1 / ((p : ℚ) - 1) ^ 2 else 1) : ℚ) : ℝ) ≤
        ((6607 / 10000 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hQ
    rwa [cast_prod201] at h2
  have hnum : ((6607 / 10000 : ℚ) : ℝ) = (0.6607 : ℝ) := by norm_num
  rw [hnum] at hR
  simpa [TaoFivePrimes.twinPrimePartial] using hR

/-- For `Q ≥ 81`, the partial product dominates `partial 80` times the telescoping
coefficient `(80 Q)/(81 (Q-1))`. -/
private lemma twinPartial_ge_80 (Q : ℕ) (hQ : 81 ≤ Q) :
    TaoFivePrimes.twinPrimePartial 80 * (((80 : ℝ) * Q) / (81 * ((Q : ℝ) - 1)))
      ≤ TaoFivePrimes.twinPrimePartial Q := by
  induction Q, hQ using Nat.le_induction with
  | base =>
    have h81 : TaoFivePrimes.twinPrimePartial 81 = TaoFivePrimes.twinPrimePartial 80 := by
      rw [TaoFivePrimes.twinPrimePartial, TaoFivePrimes.twinPrimePartial,
        Finset.prod_range_succ]
      rw [if_neg (show ¬ (Nat.Prime 81 ∧ 2 < 81) by decide), mul_one]
    rw [h81]
    have hcoef : (80 : ℝ) * ((81 : ℕ) : ℝ) / (81 * (((81 : ℕ) : ℝ) - 1)) = 1 := by
      push_cast
      norm_num
    rw [hcoef, mul_one]
  | succ Q hQ ih =>
    have hstep : TaoFivePrimes.twinPrimePartial (Q + 1) =
        TaoFivePrimes.twinPrimePartial Q *
          (if Nat.Prime (Q + 1) ∧ 2 < Q + 1 then
            1 - 1 / (((Q + 1 : ℕ) : ℝ) - 1) ^ 2 else 1) := by
      rw [TaoFivePrimes.twinPrimePartial, TaoFivePrimes.twinPrimePartial,
        Finset.prod_range_succ]
    by_cases hp : Nat.Prime (Q + 1) ∧ 2 < Q + 1
    · rw [hstep, if_pos hp]
      have hfac : (0 : ℝ) ≤ 1 - 1 / (((Q + 1 : ℕ) : ℝ) - 1) ^ 2 := by
        have hsub : (((Q + 1 : ℕ) : ℝ) - 1) = (Q : ℝ) := by push_cast; ring
        rw [hsub]
        have hQ81 : (81 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
        have hden : (1 : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
        have hle : 1 / (Q : ℝ) ^ 2 ≤ 1 := by
          rw [div_le_one (by nlinarith)]
          exact hden
        linarith
      have hkey : TaoFivePrimes.twinPrimePartial 80 *
            ((80 : ℝ) * ((Q + 1 : ℕ) : ℝ) / (81 * (((Q + 1 : ℕ) : ℝ) - 1)))
          = (TaoFivePrimes.twinPrimePartial 80 * (((80 : ℝ) * Q) / (81 * ((Q : ℝ) - 1)))) *
            (1 - 1 / (((Q + 1 : ℕ) : ℝ) - 1) ^ 2) := by
        have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
        have hQ1' : (0 : ℝ) < (Q : ℝ) - 1 := by linarith
        have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
        have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQ0
        have hQ1ne : (Q : ℝ) - 1 ≠ 0 := ne_of_gt hQ1'
        push_cast
        simp only [add_sub_cancel_right]
        field_simp
        ring
      rw [hkey]
      exact mul_le_mul_of_nonneg_right ih hfac
    · rw [hstep, if_neg hp, mul_one]
      refine le_trans ?_ ih
      have hcoef : (80 : ℝ) * ((Q + 1 : ℕ) : ℝ) / (81 * (((Q + 1 : ℕ) : ℝ) - 1))
          ≤ (80 : ℝ) * Q / (81 * ((Q : ℝ) - 1)) := by
        have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
        have hQ1' : (0 : ℝ) < (Q : ℝ) - 1 := by linarith
        have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
        push_cast
        rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
        nlinarith
      exact mul_le_mul_of_nonneg_left hcoef (twinPartial_nonneg 80)

private lemma twinPartial_ge_625 (Q : ℕ) : (0.625 : ℝ) ≤ TaoFivePrimes.twinPrimePartial Q := by
  rcases le_or_gt Q 80 with hQ | hQ
  · have hle : TaoFivePrimes.twinPrimePartial 80 ≤ TaoFivePrimes.twinPrimePartial Q := by
      rw [TaoFivePrimes.twinPrimePartial, TaoFivePrimes.twinPrimePartial]
      refine Finset.prod_le_prod_of_subset_of_le_one (s := Finset.range (Q + 1))
        (t := Finset.range 81)
        (f := fun p => if Nat.Prime p ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1) ^ 2 else 1)
        ?_ ?_ ?_
      · intro i hi
        simp only [Finset.mem_range] at hi ⊢
        omega
      · intro i _
        exact twinPartial_fac_nonneg i
      · intro i _ _
        exact twinPartial_fac_le_one i
    linarith [twinPartial_80_ge]
  · have hbig := twinPartial_ge_80 Q hQ
    have hcoef : (80 : ℝ) / 81 ≤ ((80 : ℝ) * Q) / (81 * ((Q : ℝ) - 1)) := by
      have hQ1 : (1 : ℝ) < (Q : ℝ) := by exact_mod_cast (by omega : 1 < Q)
      have hQ1' : (0 : ℝ) < (Q : ℝ) - 1 := by linarith
      rw [div_le_div_iff₀ (by norm_num) (by nlinarith)]
      nlinarith
    have h1 : TaoFivePrimes.twinPrimePartial 80 * ((80 : ℝ) / 81)
        ≤ TaoFivePrimes.twinPrimePartial Q :=
      le_trans (mul_le_mul_of_nonneg_left hcoef (twinPartial_nonneg 80)) hbig
    have h2 : (0.625 : ℝ) ≤ TaoFivePrimes.twinPrimePartial 80 * ((80 : ℝ) / 81) := by
      have h3 := mul_le_mul_of_nonneg_right twinPartial_80_ge
        (by norm_num : (0 : ℝ) ≤ (80 : ℝ) / 81)
      linarith [h3]
    linarith

/-! ## Auxiliary bounds for the prime reciprocal sum -/

private lemma log_div_le (m : ℝ) (hm : 2 ≤ m) :
    Real.log m / (m * (m - 1)) ≤ 4 * m ^ (-(3 / 2) : ℝ) := by
  have hm0 : 0 < m := by linarith
  have hden : 0 < m * (m - 1) := by nlinarith
  have hlog : Real.log m ≤ 2 * Real.sqrt m := by
    have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
    have h1 : Real.log (Real.sqrt m) ≤ Real.sqrt m - 1 :=
      Real.log_le_sub_one_of_pos hsqrt_pos
    have h2 : Real.log m = 2 * Real.log (Real.sqrt m) := by
      rw [← Real.sq_sqrt hm0.le, Real.log_pow]
      norm_num
    linarith
  have hpow : m ^ (1 / 2 : ℝ) = m ^ 2 * m ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_natCast m 2, ← Real.rpow_add hm0]
    norm_num
  rw [div_le_iff₀ hden]
  calc Real.log m ≤ 2 * Real.sqrt m := hlog
    _ = 2 * m ^ (1 / 2 : ℝ) := by rw [Real.sqrt_eq_rpow]
    _ = 2 * (m ^ 2 * m ^ (-(3 / 2) : ℝ)) := by rw [hpow]
    _ = (2 * m ^ 2) * m ^ (-(3 / 2) : ℝ) := by ring
    _ ≤ (4 * m * (m - 1)) * m ^ (-(3 / 2) : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by nlinarith)
          (Real.rpow_nonneg hm0.le _)
    _ = 4 * m ^ (-(3 / 2) : ℝ) * (m * (m - 1)) := by ring

private lemma log_201_le : Real.log 201 ≤ (5.3033173676 : ℝ) := by
  have h201 : Real.log 201 = Real.log 2 + 2 * Real.log 10 + Real.log (1.005 : ℝ) := by
    have hdecomp : (201 : ℝ) = 2 * 10 ^ 2 * 1.005 := by norm_num
    rw [hdecomp, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [h201]
  have h10 : Real.log 10 ≤ (2.3025850934 : ℝ) := by
    have hsplit : Real.log 10 = Real.log 2 + Real.log 5 := by
      rw [show (10 : ℝ) = 2 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [hsplit]
    linarith [Real.log_two_lt_d9, Real.log_five_lt_d9]
  have hsmall : Real.log (1.005 : ℝ) ≤ (0.005 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.005)
    linarith
  linarith [Real.log_two_lt_d9, h10, hsmall]

theorem solution :
    (1.25 : ℝ) ≤ TaoFivePrimes.twinPrimeConstant ∧
      TaoFivePrimes.twinPrimeConstant ≤ 1.3217 ∧
      (0.5722 : ℝ) ≤ Real.eulerMascheroniConstant ∧
      (0.74 : ℝ) ≤
        ∑' p : Nat.Primes,
          Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold TaoFivePrimes.twinPrimeConstant
    have hne : (Set.range TaoFivePrimes.twinPrimePartial).Nonempty := ⟨_, 0, rfl⟩
    have hsInf : (0.625 : ℝ) ≤ sInf (Set.range TaoFivePrimes.twinPrimePartial) :=
      le_csInf hne (by rintro _ ⟨Q, rfl⟩; exact twinPartial_ge_625 Q)
    linarith
  · unfold TaoFivePrimes.twinPrimeConstant
    have hbdd : BddBelow (Set.range TaoFivePrimes.twinPrimePartial) :=
      ⟨0, by rintro _ ⟨Q, rfl⟩; exact twinPartial_nonneg Q⟩
    have hsInf : sInf (Set.range TaoFivePrimes.twinPrimePartial)
        ≤ TaoFivePrimes.twinPrimePartial 200 :=
      csInf_le hbdd ⟨200, rfl⟩
    linarith [hsInf, twinPartial_200_le]
  · have hlt := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 200
    have heq : Real.eulerMascheroniSeq 200 = (harmonic 200 : ℝ) - Real.log 201 := by
      rw [Real.eulerMascheroniSeq]
      congr 1
      norm_num
    rw [heq] at hlt
    have hH : (5.878 : ℝ) ≤ (harmonic 200 : ℝ) := by
      have hQ : (5878 / 1000 : ℚ) ≤ harmonic 200 := by decide +kernel
      have hcast : ((5878 / 1000 : ℚ) : ℝ) ≤ (harmonic 200 : ℝ) := Rat.cast_le.mpr hQ
      have hnum : ((5878 / 1000 : ℚ) : ℝ) = (5.878 : ℝ) := by norm_num
      rwa [hnum] at hcast
    linarith [hlt, hH, log_201_le]
  · set g : ℕ → ℝ := fun n =>
      if Nat.Prime n then Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) else 0 with hgdef
    have hga : ∀ n, g n = if Nat.Prime n then
        Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) else 0 := by
      intro n
      rw [hgdef]
    have hg_ind : g = {n | Nat.Prime n}.indicator
        (fun n => Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1))) := by
      funext n
      by_cases hp : Nat.Prime n
      · rw [hga, Set.indicator_of_mem (show n ∈ {m | Nat.Prime m} from hp), if_pos hp]
      · rw [hga, Set.indicator_of_notMem (show n ∉ {m | Nat.Prime m} from hp), if_neg hp]
    have hg_sum : ∑' n : ℕ, g n
        = ∑' p : Nat.Primes, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
      rw [hg_ind]
      unfold Nat.Primes
      rw [← tsum_subtype]
      rfl
    rw [← hg_sum]
    have hg_nonneg : ∀ n, 0 ≤ g n := by
      intro n
      by_cases hp : Nat.Prime n
      · rw [hga, if_pos hp]
        have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hp.one_le
        have hden : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
        exact div_nonneg (Real.log_nonneg hn1) hden
      · rw [hga, if_neg hp]
    have hg_le : ∀ n, g n ≤ 4 * (n : ℝ) ^ (-(3 / 2) : ℝ) := by
      intro n
      rcases lt_or_ge n 2 with hn | hn
      · interval_cases n
        · rw [hga, if_neg (show ¬ Nat.Prime 0 by decide)]
          positivity
        · rw [hga, if_neg (show ¬ Nat.Prime 1 by decide)]
          positivity
      · rw [hga]
        by_cases hp : Nat.Prime n
        · rw [if_pos hp]
          exact log_div_le (n : ℝ) (by exact_mod_cast hn)
        · rw [if_neg hp]
          exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    have hg_summable : Summable g :=
      Summable.of_nonneg_of_le hg_nonneg hg_le
        ((Real.summable_nat_rpow.mpr (by norm_num : (-(3 / 2) : ℝ) < -1)).mul_left 4)
    have hs : (0.74 : ℝ) ≤ ∑ n ∈ (Finset.range 301).filter Nat.Prime, g n := by
      have heq_sum : ∑ n ∈ (Finset.range 301).filter Nat.Prime, g n
          = ∑ n ∈ (Finset.range 301).filter Nat.Prime,
              Real.log (n : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hga, if_pos (Finset.mem_filter.mp hn).2]
      rw [heq_sum]
      have hQ : (37 / 50 : ℚ) ≤
          ∑ n ∈ (Finset.range 301).filter Nat.Prime,
            cval n n.log2 / ((n : ℚ) * ((n : ℚ) - 1)) := by
        decide +kernel
      have hcast : ((∑ n ∈ (Finset.range 301).filter Nat.Prime,
            cval n n.log2 / ((n : ℚ) * ((n : ℚ) - 1)) : ℚ) : ℝ)
          = ∑ n ∈ (Finset.range 301).filter Nat.Prime,
              ((cval n n.log2 : ℚ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
        push_cast
        rfl
      have hR : (0.74 : ℝ) ≤
          ∑ n ∈ (Finset.range 301).filter Nat.Prime,
            ((cval n n.log2 : ℚ) : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
        have h2 : (((37 / 50 : ℚ)) : ℝ) ≤
            ((∑ n ∈ (Finset.range 301).filter Nat.Prime,
              cval n n.log2 / ((n : ℚ) * ((n : ℚ) - 1)) : ℚ) : ℝ) :=
          Rat.cast_le.mpr hQ
        rw [hcast] at h2
        have hnum : (((37 / 50 : ℚ)) : ℝ) = (0.74 : ℝ) := by norm_num
        rw [hnum] at h2
        exact h2
      refine le_trans hR ?_
      apply Finset.sum_le_sum
      intro n hn
      have hpn : Nat.Prime n := (Finset.mem_filter.mp hn).2
      have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpn.two_le
      have hden : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
      exact div_le_div_of_nonneg_right (cval_le_log n hpn.pos) hden
    have hle_tsum := hg_summable.sum_le_tsum ((Finset.range 301).filter Nat.Prime)
      (fun n _ => hg_nonneg n)
    linarith [hs, hle_tsum]
