-- Prove2me | solution 1 for ZetaNine.HarmonicStability.harmonic_finite_prime_log_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-02T14:53:33.466416+00:00
-- url     : https://prove2.me/submissions/3ee9c8f8-ed5a-4013-902e-3be45596e25c

import Definitions.Def_ZetaNine_HarmonicPrimeValuation
import Definitions.Def_ZetaNine_HarmonicStability
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Tactic

/-!
# Exact large-prime denominator valuations of actual harmonic sums

This file addresses the finite-prime-block arithmetic in sections 1--2 of
`harmonic-denominator-stability-2026-10-01.md`. The harmonic sum here is the
same rational object as in the shared definition module. No prime number
theorem or harmonic denominator asymptotic is assumed.
-/

set_option autoImplicit false
open scoped BigOperators

namespace ZetaNine.HarmonicStability



private theorem den_sum_coprime {ι : Type*} (S : Finset ι) (f : ι → ℚ) (p : ℕ)
    (h : ∀ i ∈ S, p.Coprime (f i).den) : p.Coprime (∑ i ∈ S, f i).den := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact ((h i (Finset.mem_insert_self _ _)).mul_right
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))).of_dvd_right
        (Rat.add_den_dvd _ _)

private theorem reciprocal_den_coprime (s j p : ℕ) (hj : 0 < j)
    (hpj : p.Coprime j) : p.Coprime (1 / (j : ℚ) ^ s).den := by
  rw [one_div, ← inv_pow, Rat.den_pow, Rat.inv_natCast_den_of_pos hj]
  exact hpj.pow_right s

/-- The actual nonmultiple remainder has denominator prime to `p`, with no
endpoint restriction; all cancellation is allowed. -/
theorem primeRemainder_den_coprime (s N p : ℕ) (hp : p.Prime) :
    p.Coprime (primeRemainder s N p).den := by
  apply den_sum_coprime
  intro j hj
  rcases Finset.mem_filter.mp hj with ⟨hj, hnot⟩
  exact reciprocal_den_coprime s j p (Finset.mem_Icc.mp hj).1
    (hp.coprime_iff_not_dvd.mpr hnot)

private theorem multiple_indices (N p : ℕ) (hp : 0 < p) :
    (Finset.Icc 1 N).filter (fun j => p ∣ j) =
      (Finset.Icc 1 (N / p)).image (fun k => p * k) := by
  classical
  ext j
  constructor
  · intro hj
    rcases Finset.mem_filter.mp hj with ⟨hj, hdvd⟩
    rcases hdvd with ⟨k, rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨k, Finset.mem_Icc.mpr ⟨?_, ?_⟩, rfl⟩
    · have : 0 < p * k := (Finset.mem_Icc.mp hj).1
      exact Nat.pos_of_mul_pos_left this
    · apply (Nat.le_div_iff_mul_le hp).mpr
      simpa only [mul_comm] using (Finset.mem_Icc.mp hj).2
  · intro hj
    rcases Finset.mem_image.mp hj with ⟨k, hk, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, dvd_mul_right p k⟩
    · exact Nat.mul_pos hp (Finset.mem_Icc.mp hk).1
    · have := (Nat.le_div_iff_mul_le hp).mp (Finset.mem_Icc.mp hk).2
      simpa only [mul_comm] using this

/-- All-parameter exact splitting of the real finite harmonic object.
The extra condition `N < p^2` is needed only for the unit prefix argument,
not for this equality. -/
theorem harmonic_split_prime (s N p : ℕ) (hp : 0 < p) :
    harmonicPower s N = (p : ℚ)⁻¹ ^ s * harmonicPower s (N / p) +
      primeRemainder s N p := by
  classical
  unfold harmonicPower primeRemainder
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun j => p ∣ j)]
  congr 1
  rw [multiple_indices N p hp, Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Nat.cast_mul, mul_pow, one_div, mul_inv_rev, inv_pow]
    ring
  · intro a ha b hb hab
    exact Nat.eq_of_mul_eq_mul_left hp hab

/-- The same exact splitting in the scaled form of equation (1) in the
original research note. -/
theorem harmonic_scaled_split_prime (s N p : ℕ) (hp : 0 < p) :
    (p : ℚ) ^ s * harmonicPower s N = harmonicPower s (N / p) +
      (p : ℚ) ^ s * primeRemainder s N p := by
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  rw [harmonic_split_prime s N p hp, mul_add, ← mul_assoc, ← mul_pow,
    mul_inv_cancel₀ hpq, one_pow, one_mul]

/-- Every order and endpoint give a positive actual prefix when it contains
the term at 1. This supplies nonzero numerators for fixed finite blocks. -/
theorem harmonicPower_pos (s N : ℕ) (hN : 0 < N) : 0 < harmonicPower s N := by
  unfold harmonicPower
  apply Finset.sum_pos
  · intro j hj
    have hjpos : 0 < (j : ℚ) := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    exact div_pos zero_lt_one (pow_pos hjpos s)
  · exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩⟩

/-- `p^2>N` makes the actual prefix denominator a p-unit. -/
theorem harmonic_prefix_den_coprime (s N p : ℕ) (hp : p.Prime)
    (hN : N < p ^ 2) : p.Coprime (harmonicPower s (N / p)).den := by
  apply den_sum_coprime
  intro j hj
  have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
  have hjlt : j < p := lt_of_le_of_lt (Finset.mem_Icc.mp hj).2
    ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by simpa only [pow_two] using hN))
  exact reciprocal_den_coprime s j p hjpos (hp.coprime_iff_not_dvd.mpr
    (fun hdvd => (Nat.le_of_dvd hjpos hdvd).not_gt hjlt))

private theorem valuation_nonneg_of_den_coprime (q : ℚ) (p : ℕ) (hp : p.Prime)
    (hq : p.Coprime q.den) : 0 ≤ padicValRat p q := by
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd
    (hp.coprime_iff_not_dvd.mp hq)]
  simp

private theorem valuation_den_of_negative (q : ℚ) (p s : ℕ) (hp : p.Prime)
    (hs : 0 < s) (hv : padicValRat p q = -(s : ℤ)) : padicValNat p q.den = s := by
  have hnot : ¬ p ∣ q.num.natAbs := by
    intro hdvd
    have hcop : p.Coprime q.den := q.reduced.of_dvd_left hdvd
    have hn := valuation_nonneg_of_den_coprime q p hp hcop
    rw [hv] at hn
    exact (neg_neg_of_pos (show (0 : ℤ) < s by exact_mod_cast hs)).not_ge hn
  rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hnot] at hv
  simpa using congrArg Int.natAbs hv

/-- The exact unit-prefix assertion used in the original finite-block
argument. The hypotheses concern the reduced numerator of the actual
prefix, not a substituted coefficient. -/
theorem harmonic_large_prime_valuation (s N p : ℕ) (hp : p.Prime)
    (hs : 0 < s) (hNp : p ≤ N) (hN : N < p ^ 2)
    (hunit : ¬ p ∣ (harmonicPower s (N / p)).num.natAbs) :
    padicValRat p (harmonicPower s N) = -(s : ℤ) := by
  let : Fact p.Prime := ⟨hp⟩
  have hprefixpos := harmonicPower_pos s (N / p)
    ((Nat.le_div_iff_mul_le hp.pos).mpr (by simpa using hNp))
  have hprefixne := ne_of_gt hprefixpos
  have hprefixval : padicValRat p (harmonicPower s (N / p)) = 0 := by
    rw [padicValRat_def, padicValInt, padicValNat.eq_zero_of_not_dvd hunit,
      padicValNat.eq_zero_of_not_dvd
        (hp.coprime_iff_not_dvd.mp (harmonic_prefix_den_coprime s N p hp hN))]
    simp
  have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have htermne : (p : ℚ)⁻¹ ^ s * harmonicPower s (N / p) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (inv_ne_zero hpq)) hprefixne
  have htermval : padicValRat p ((p : ℚ)⁻¹ ^ s * harmonicPower s (N / p)) =
      -(s : ℤ) := by
    rw [padicValRat.mul (pow_ne_zero _ (inv_ne_zero hpq)) hprefixne,
      padicValRat.pow, padicValRat.inv, padicValRat.self hp.one_lt, hprefixval]
    ring
  rw [harmonic_split_prime s N p hp.pos]
  by_cases hr : primeRemainder s N p = 0
  · simpa only [hr, add_zero] using htermval
  · have hnonzero : (p : ℚ)⁻¹ ^ s * harmonicPower s (N / p) +
        primeRemainder s N p ≠ 0 := by
      rw [← harmonic_split_prime s N p hp.pos]
      exact ne_of_gt (harmonicPower_pos s N (lt_of_lt_of_le hp.pos hNp))
    rw [padicValRat.add_eq_of_lt hnonzero htermne hr]
    · exact htermval
    · rw [htermval]
      exact lt_of_lt_of_le (neg_neg_of_pos (show (0 : ℤ) < s by exact_mod_cast hs))
        (valuation_nonneg_of_den_coprime _ p hp (primeRemainder_den_coprime s N p hp))

/-- The full reduced positive denominator has exactly exponent `s`.
Reducedness, rather than an arbitrary denominator presentation, converts
the proved negative rational valuation into this natural valuation. -/
theorem harmonic_large_prime_den_valuation (s N p : ℕ) (hp : p.Prime)
    (hs : 0 < s) (hNp : p ≤ N) (hN : N < p ^ 2)
    (hunit : ¬ p ∣ (harmonicPower s (N / p)).num.natAbs) :
    padicValNat p (harmonicPower s N).den = s :=
  valuation_den_of_negative _ p s hp hs
    (harmonic_large_prime_valuation s N p hp hs hNp hN hunit)

/-- The first full block needs no exceptional-prime assumption: the prefix
is exactly `H₁=1`. This is uniform in the order and in every endpoint of
the interval `p ≤ N < 2p`. -/
theorem harmonic_first_block_den_valuation (s N p : ℕ) (hp : p.Prime)
    (hs : 0 < s) (hNp : p ≤ N) (hN : N < 2 * p) :
    padicValNat p (harmonicPower s N).den = s := by
  have hdiv : N / p = 1 := by
    have hlo : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp.pos).mpr (by simpa using hNp)
    have hhi : N / p < 2 := (Nat.div_lt_iff_lt_mul hp.pos).mpr hN
    omega
  apply harmonic_large_prime_den_valuation s N p hp hs hNp
  · have hp2 := hp.two_le
    nlinarith [hN]
  · simpa only [hdiv, harmonicPower, Finset.Icc_self, Finset.sum_singleton,
      Nat.cast_one, one_pow, div_self (one_ne_zero : (1 : ℚ) ≠ 0), Rat.num_one,
      Int.natAbs_one] using hp.not_dvd_one



theorem harmonicExceptionalProduct_pos (s K : ℕ) :
    0 < harmonicExceptionalProduct s K := by
  apply Finset.prod_pos
  intro k hk
  apply Nat.pos_of_ne_zero
  exact Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr
    (ne_of_gt (harmonicPower_pos s k (Finset.mem_Icc.mp hk).1)))

/-- Prime divisors of any prefix numerator in a fixed finite block occur
in the explicit exception product. This direction does not claim that
all primes are units, and so retains the original exceptional-prime issue. -/
theorem harmonic_prefix_num_dvd_exceptional (s K k : ℕ) (hk : k ∈ Finset.Icc 1 K) :
    (harmonicPower s k).num.natAbs ∣ harmonicExceptionalProduct s K :=
  Finset.dvd_prod_of_mem (fun k => (harmonicPower s k).num.natAbs) hk

/-- Complete arithmetic for any fixed finite collection of floor blocks.
The explicit bound on the exception product supplies the unit condition;
the conclusion is derived for the original harmonic sum. -/
theorem harmonic_finite_blocks_den_valuation (s K N p : ℕ) (hp : p.Prime)
    (hs : 0 < s) (hNp : p ≤ N) (hblock : N / p ≤ K) (hpK : K < p)
    (hexception : harmonicExceptionalProduct s K < p) :
    padicValNat p (harmonicPower s N).den = s := by
  have hprefixlo : 1 ≤ N / p := (Nat.le_div_iff_mul_le hp.pos).mpr (by simpa using hNp)
  have hNbound : N < (K + 1) * p :=
    (Nat.div_lt_iff_lt_mul hp.pos).mp (Nat.lt_succ_of_le hblock)
  have hN : N < p ^ 2 := by
    rw [pow_two]
    exact lt_of_lt_of_le hNbound (Nat.mul_le_mul_right p hpK)
  apply harmonic_large_prime_den_valuation s N p hp hs hNp hN
  intro hdvd
  have hexcdiv := hdvd.trans (harmonic_prefix_num_dvd_exceptional s K (N / p)
    (Finset.mem_Icc.mpr ⟨hprefixlo, hblock⟩))
  exact (Nat.le_of_dvd (harmonicExceptionalProduct_pos s K) hexcdiv).not_gt hexception

private theorem distinct_prime_powers_prod_dvd (S : Finset ℕ) (s D : ℕ)
    (hprime : ∀ p ∈ S, p.Prime) (hdvd : ∀ p ∈ S, p ^ s ∣ D) :
    (∏ p ∈ S, p ^ s) ∣ D := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    rw [Finset.prod_insert hp]
    have hcop : (p ^ s).Coprime (∏ q ∈ S, q ^ s) := by
      apply Nat.coprime_prod_right_iff.mpr
      intro q hq
      apply Nat.Coprime.pow
      exact (Nat.coprime_primes (hprime p (Finset.mem_insert_self _ _))
        (hprime q (Finset.mem_insert_of_mem hq))).mpr
          (fun heq => hp (heq ▸ hq))
    exact hcop.mul_dvd_of_dvd_of_dvd (hdvd p (Finset.mem_insert_self _ _))
      (ih (fun q hq => hprime q (Finset.mem_insert_of_mem hq))
        (fun q hq => hdvd q (Finset.mem_insert_of_mem hq)))

/-- Every finite prime set in the admitted fixed blocks contributes its
full `s`th-power product to the actual reduced denominator. This is the
unconditional arithmetic ingredient of the PNT lower-bound argument. -/
theorem harmonic_finite_prime_product_dvd (s K N : ℕ) (S : Finset ℕ)
    (hs : 0 < s)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ N / p ≤ K ∧ K < p ∧
      harmonicExceptionalProduct s K < p) :
    (∏ p ∈ S, p ^ s) ∣ (harmonicPower s N).den := by
  apply distinct_prime_powers_prod_dvd
  · intro p hp
    exact (hS p hp).1
  · intro p hp
    rcases hS p hp with ⟨hprime, hNp, hblock, hpK, hexc⟩
    let : Fact p.Prime := ⟨hprime⟩
    apply (padicValNat_dvd_iff_le (Rat.den_nz _)).mpr
    rw [harmonic_finite_blocks_den_valuation s K N p hprime hs hNp hblock hpK hexc]

/-- The literal finite logarithmic lower bound used before applying the
prime number theorem. There is no asymptotic or prime-distribution
hypothesis here, and the denominator is fully reduced. -/
theorem checked_harmonic_finite_prime_log_lower_bound (s K N : ℕ) (S : Finset ℕ)
    (hs : 0 < s)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ N / p ≤ K ∧ K < p ∧
      harmonicExceptionalProduct s K < p) :
    (s : ℝ) * (∑ p ∈ S, Real.log (p : ℝ)) ≤ logDen (harmonicPower s N) := by
  have hprodpos : 0 < ∏ p ∈ S, p ^ s :=
    Finset.prod_pos (fun p hp => pow_pos (hS p hp).1.pos s)
  have hle : (∏ p ∈ S, p ^ s) ≤ (harmonicPower s N).den :=
    Nat.le_of_dvd (Rat.den_pos _) (harmonic_finite_prime_product_dvd s K N S hs hS)
  have hlog := Real.log_le_log
    (show (0 : ℝ) < ((∏ p ∈ S, p ^ s : ℕ) : ℝ) by exact_mod_cast hprodpos)
    (show ((∏ p ∈ S, p ^ s : ℕ) : ℝ) ≤ ((harmonicPower s N).den : ℝ) by
      exact_mod_cast hle)
  have hprodlog : Real.log ((∏ p ∈ S, p ^ s : ℕ) : ℝ) =
      (s : ℝ) * (∑ p ∈ S, Real.log (p : ℝ)) := by
    rw [Nat.cast_prod, Real.log_prod]
    · simp_rw [Nat.cast_pow, Real.log_pow]
      rw [Finset.mul_sum]
    · intro p hp
      exact_mod_cast pow_ne_zero s (hS p hp).1.ne_zero
  simpa only [hprodlog, logDen] using hlog


end ZetaNine.HarmonicStability

open ZetaNine.HarmonicStability

theorem solution (s K N : ℕ) (S : Finset ℕ)
    (hs : 0 < s)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ N ∧ N / p ≤ K ∧ K < p ∧
      harmonicExceptionalProduct s K < p) :
    (s : ℝ) * (∑ p ∈ S, Real.log (p : ℝ)) ≤ logDen (harmonicPower s N) := by
  exact ZetaNine.HarmonicStability.checked_harmonic_finite_prime_log_lower_bound s K N S hs hS

#print axioms solution
