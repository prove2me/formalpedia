-- Prove2me | solution 1 for ZetaNine.HarmonicStability.harmonic_nine_double_log_den_rate
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-03T14:09:18.009084+00:00
-- url     : https://prove2.me/submissions/b95e35c4-f180-44ce-aad7-5c081ed3b325

import Definitions.Def_ZetaNine_HarmonicStability
import Definitions.Def_ZetaNine_HarmonicPrimeValuation
import Theorems.Thm_MediumPNT
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.Basic









/-!
# Rational perturbation stability for generalized harmonic denominators

This file formalizes the unconditional denominator inequalities in Lemma 2
of `harmonic-denominator-stability-2026-10-01.md`, their general limit
transfer, and the all-parameter finite lcm clearing bound. It does not assume
or introduce a prime-number-theorem axiom. The harmonic denominator's exact
prime-number-theorem growth rate remains outside this file's current scope.
-/

set_option autoImplicit false

open scoped BigOperators
open Filter

namespace ZetaNine.HarmonicStability



/-- Both divisibilities survive every possible numerator cancellation. -/
theorem denominator_stability (h r : ℚ) :
    (h + r).den ∣ h.den * r.den ∧ h.den ∣ (h + r).den * r.den := by
  constructor
  · exact Rat.add_den_dvd h r
  · simpa only [add_sub_cancel_right] using Rat.sub_den_dvd (h + r) r



private theorem logDen_le_logDen_add (h r : ℚ) :
    logDen (h + r) ≤ logDen h + logDen r := by
  have hd := (denominator_stability h r).1
  have hle : (h + r).den ≤ h.den * r.den :=
    Nat.le_of_dvd (Nat.mul_pos (Rat.den_pos h) (Rat.den_pos r)) hd
  have hr : (h + r).den > 0 := Rat.den_pos (h + r)
  have hl := Real.log_le_log (show (0 : ℝ) < ((h + r).den : ℝ) by exact_mod_cast hr)
    (show (((h + r).den : ℕ) : ℝ) ≤ ((h.den * r.den : ℕ) : ℝ) by exact_mod_cast hle)
  simpa only [Nat.cast_mul,
    Real.log_mul (show (h.den : ℝ) ≠ 0 by exact_mod_cast Rat.den_nz h)
      (show (r.den : ℝ) ≠ 0 by exact_mod_cast Rat.den_nz r), logDen] using hl

/-- The exact logarithmic form of the original rational perturbation lemma.
There is no restriction on the size or sign of either numerator. -/
theorem log_denominator_stability (h r : ℚ) :
    |logDen (h + r) - logDen h| ≤ logDen r := by
  have hu := logDen_le_logDen_add h r
  have hl : logDen h ≤ logDen (h + r) + logDen r := by
    have ht := logDen_le_logDen_add (h + r) (-r)
    simpa only [add_neg_cancel_right, logDen, Rat.neg_den] using ht
  exact abs_le.mpr ⟨by linarith, by linarith⟩



private theorem den_sum_dvd {ι : Type*} (S : Finset ι) (f : ι → ℚ) (D : ℕ)
    (h : ∀ i ∈ S, (f i).den ∣ D) : (∑ i ∈ S, f i).den ∣ D := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (Rat.add_den_dvd_lcm _ _).trans
      (Nat.lcm_dvd (h i (Finset.mem_insert_self _ _))
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))))

/-- The finite upper arithmetic bound in the original harmonic-rate proof,
for the actual reduced denominator and the actual finite lcm. -/
theorem checked_harmonic_den_dvd_lcm_power (s N : ℕ) :
    (harmonicPower s N).den ∣ Nat.lcmUpto N ^ s := by
  apply den_sum_dvd
  intro j hj
  have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
  have hjdvd : j ∣ Nat.lcmUpto N := Finset.dvd_lcm hj
  rw [one_div, ← inv_pow, Rat.den_pow, Rat.inv_natCast_den_of_pos hjpos]
  exact pow_dvd_pow_of_dvd hjdvd s

/-- The finite logarithmic upper bound for the actual harmonic denominator. -/
theorem harmonic_log_den_le_lcm (s N : ℕ) :
    logDen (harmonicPower s N) ≤ (s : ℝ) * Real.log (Nat.lcmUpto N : ℝ) := by
  have hle : (harmonicPower s N).den ≤ Nat.lcmUpto N ^ s :=
    Nat.le_of_dvd (pow_pos (Nat.lcmUpto_pos N) s) (checked_harmonic_den_dvd_lcm_power s N)
  have ht := Real.log_le_log
    (show (0 : ℝ) < ((harmonicPower s N).den : ℝ) by
      exact_mod_cast Rat.den_pos (harmonicPower s N))
    (show (((harmonicPower s N).den : ℕ) : ℝ) ≤ ((Nat.lcmUpto N ^ s : ℕ) : ℝ) by
      exact_mod_cast hle)
  simpa only [Nat.cast_pow, Real.log_pow, logDen] using ht



/-- General denominator-rate stability, deduced from the actual arithmetic
denominator inequality rather than assumed for the perturbed sequence. -/
theorem log_den_rate_stability {ι : Type*} (l : Filter ι)
    (h r : ι → ℚ) (scale : ι → ℝ) (hscale : ∀ i, 0 ≤ scale i) (a : ℝ)
    (hh : Tendsto (fun i => logDen (h i) / scale i) l (nhds a))
    (hr : Tendsto (fun i => logDen (r i) / scale i) l (nhds 0)) :
    Tendsto (fun i => logDen (h i + r i) / scale i) l (nhds a) := by
  apply tendsto_of_tendsto_of_dist hh
  refine squeeze_zero (g := fun i => logDen (r i) / scale i) (fun i => dist_nonneg) ?_ hr
  intro i
  rw [Real.dist_eq, ← sub_div, abs_div, abs_of_nonneg (hscale i), abs_sub_comm]
  exact div_le_div_of_nonneg_right (log_denominator_stability (h i) (r i)) (hscale i)



/-- Application of the proved general stability theorem to the original
harmonic corollary. The baseline rate `hh` is the separate PNT-dependent
Theorem 1; it is explicitly a hypothesis here, not an unproved Lean axiom. -/
theorem harmonic_log_den_rate_stability (s : ℕ) (r : ℕ → ℚ)
    (hh : Tendsto (fun N => logDen (harmonicPower s N) / (N : ℝ)) atTop (nhds (s : ℝ)))
    (hr : Tendsto (fun N => logDen (r N) / (N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N => logDen (harmonicPower s N + r N) / (N : ℝ))
      atTop (nhds (s : ℝ)) :=
  log_den_rate_stability atTop (harmonicPower s) r (fun N => (N : ℝ))
    (fun N => Nat.cast_nonneg N) (s : ℝ) hh hr


end ZetaNine.HarmonicStability

open ZetaNine.HarmonicStability












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
theorem harmonic_finite_prime_log_lower_bound (s K N : ℕ) (S : Finset ℕ)
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









/-!
# The actual harmonic denominator rate, conditional only on two PNT inputs

The fixed Mathlib revision supplies Chebyshev functions and elementary
bounds, but no theorem asserting their PNT asymptotics. We therefore keep
the two prime-distribution limits as explicit hypotheses. In particular,
the harmonic denominator baseline itself is never a hypothesis.

The finite prime interval is the real interval `(N/(K+1),N]`; the exceptional
cutoff is built from the actual reduced numerators of `H₁,…,H_K`.
-/

set_option autoImplicit false
open scoped BigOperators
open Filter

namespace ZetaNine.HarmonicStability

/-- Literal primes in `(N/(K+1),N]`, with a fixed floor-block cutoff `K`. -/
noncomputable def harmonicPrimeBlock (N K : ℕ) : Finset ℕ :=
  (Nat.primesLE N).filter (fun p => (N : ℝ) / (K + 1 : ℕ) < (p : ℝ))

theorem mem_harmonicPrimeBlock (N K p : ℕ) :
    p ∈ harmonicPrimeBlock N K ↔
      p ≤ N ∧ p.Prime ∧ N < (K + 1) * p := by
  simp only [harmonicPrimeBlock, Finset.mem_filter, Nat.mem_primesLE]
  have hK : (0 : ℝ) < (K + 1 : ℕ) := by positivity
  rw [div_lt_iff₀ hK]
  norm_cast
  simp only [mul_comm, and_assoc]

/-- The lower finite logarithmic sum is exactly a difference of the actual
Mathlib Chebyshev functions; no prime counting substitute is introduced. -/
theorem harmonicPrimeBlock_log_sum (N K : ℕ) :
    (∑ p ∈ harmonicPrimeBlock N K, Real.log (p : ℝ)) =
      Chebyshev.theta (N : ℝ) - Chebyshev.theta ((N : ℝ) / (K + 1 : ℕ)) := by
  classical
  have hK : (0 : ℝ) < (K + 1 : ℕ) := by positivity
  have hnonneg : 0 ≤ (N : ℝ) / (K + 1 : ℕ) := by positivity
  have hbound : (N : ℝ) / (K + 1 : ℕ) ≤ (N : ℝ) := by
    apply div_le_self (Nat.cast_nonneg N)
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le K)
  have hlow : (Nat.primesLE N).filter
      (fun p : ℕ => ¬ (N : ℝ) / (K + 1 : ℕ) < (p : ℝ)) =
        Nat.primesLE ⌊(N : ℝ) / (K + 1 : ℕ)⌋₊ := by
    ext p
    simp only [Finset.mem_filter, Nat.mem_primesLE, not_lt]
    rw [Nat.le_floor_iff hnonneg]
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · intro h
      exact ⟨⟨by exact_mod_cast h.1.trans hbound, h.2⟩, h.1⟩
  have hsum := Finset.sum_filter_add_sum_filter_not (Nat.primesLE N)
    (fun p => (N : ℝ) / (K + 1 : ℕ) < (p : ℝ))
    (fun p => Real.log (p : ℝ))
  rw [hlow, ← Chebyshev.theta_eq_sum_primesLE,
    ← Chebyshev.theta_eq_sum_primesLE_log] at hsum
  exact eq_sub_iff_add_eq.mpr hsum

/-- An explicit endpoint after which every prime in the fixed interval is
beyond all actual finite exceptional numerator primes. -/
def harmonicPrimeBlockThreshold (s K : ℕ) : ℕ :=
  (K + 1) * (max K (harmonicExceptionalProduct s K) + 1)

theorem harmonicPrimeBlock_conditions (s K N p : ℕ)
    (hN : harmonicPrimeBlockThreshold s K ≤ N)
    (hp : p ∈ harmonicPrimeBlock N K) :
    p.Prime ∧ p ≤ N ∧ N / p ≤ K ∧ K < p ∧ harmonicExceptionalProduct s K < p := by
  obtain ⟨hpN, hprime, hblock⟩ := (mem_harmonicPrimeBlock N K p).mp hp
  have hlarge : max K (harmonicExceptionalProduct s K) < p := by
    by_contra hnot
    have hpbound : p ≤ max K (harmonicExceptionalProduct s K) := by omega
    have hmul := Nat.mul_le_mul_left (K + 1) hpbound
    unfold harmonicPrimeBlockThreshold at hN
    nlinarith
  refine ⟨hprime, hpN, ?_, lt_of_le_of_lt (le_max_left _ _) hlarge,
    lt_of_le_of_lt (le_max_right _ _) hlarge⟩
  exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hprime.pos).mpr hblock)

/-- Unconditional eventual lower bound for the actual reduced denominator,
with an explicit fixed exceptional cutoff and the literal prime interval. -/
theorem harmonic_log_den_lower_bound (s K N : ℕ) (hs : 0 < s)
    (hN : harmonicPrimeBlockThreshold s K ≤ N) :
    (s : ℝ) * (Chebyshev.theta (N : ℝ) -
      Chebyshev.theta ((N : ℝ) / (K + 1 : ℕ))) ≤ logDen (harmonicPower s N) := by
  rw [← harmonicPrimeBlock_log_sum]
  exact harmonic_finite_prime_log_lower_bound s K N (harmonicPrimeBlock N K) hs
    (fun p hp => harmonicPrimeBlock_conditions s K N p hN hp)

/-- The prime-number-theorem input for the actual first Chebyshev function.
It is a proposition supplied as an argument, not a declared axiom. -/
def ThetaPNT : Prop :=
  Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (nhds 1)

/-- The second PNT input, in the exact lcm form needed by the upper bound. -/
def LcmPNT : Prop :=
  Tendsto (fun N : ℕ => Real.log (Nat.lcmUpto N : ℝ) / (N : ℝ)) atTop (nhds 1)

private theorem theta_block_rate (K : ℕ) (hθ : ThetaPNT) :
    Tendsto (fun N : ℕ =>
      (Chebyshev.theta (N : ℝ) - Chebyshev.theta ((N : ℝ) / (K + 1 : ℕ))) /
        (N : ℝ)) atTop (nhds (1 - 1 / (K + 1 : ℕ))) := by
  have hK : (0 : ℝ) < (K + 1 : ℕ) := by positivity
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hscaled : Tendsto (fun N : ℕ => (N : ℝ) / (K + 1 : ℕ)) atTop atTop :=
    hnat.atTop_div_const hK
  have hcut := (hθ.comp hscaled).mul_const (1 / (K + 1 : ℕ) : ℝ)
  simp only [one_mul] at hcut
  have hcut' : Tendsto (fun N : ℕ =>
      Chebyshev.theta ((N : ℝ) / (K + 1 : ℕ)) / (N : ℝ))
        atTop (nhds (1 / (K + 1 : ℕ) : ℝ)) := by
    apply hcut.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    dsimp only [Function.comp_def]
    field_simp
  convert (hθ.comp hnat).sub hcut' using 1
  ext N
  exact sub_div _ _ _

/-- The complete full-sequence baseline transfer: actual harmonic
denominators have rate `s`, conditional only on the stated two prime
distribution inputs. All arithmetic and exceptional-prime exclusions are
proved above, and there is no hypothesis about harmonic denominator growth. -/
theorem harmonic_log_den_rate_of_pnt (s : ℕ) (hs : 0 < s)
    (hθ : ThetaPNT) (hℓ : LcmPNT) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N) / (N : ℝ))
      atTop (nhds (s : ℝ)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hKlim : Tendsto (fun K : ℕ =>
        (s : ℝ) * (1 - 1 / (K + 1 : ℕ))) atTop (nhds (s : ℝ)) := by
      convert (tendsto_const_nhds (x := (s : ℝ))).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))) using 1 <;> simp
    obtain ⟨K, hKa⟩ := (hKlim.eventually (eventually_gt_nhds ha)).exists
    have hlowlim := (theta_block_rate K hθ).const_mul (s : ℝ)
    have hlowevent := hlowlim.eventually (eventually_gt_nhds hKa)
    filter_upwards [hlowevent, eventually_ge_atTop (harmonicPrimeBlockThreshold s K)]
      with N hlower hN
    have hbound := div_le_div_of_nonneg_right
      (harmonic_log_den_lower_bound s K N hs hN) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    rw [mul_div_assoc] at hbound
    exact hlower.trans_le hbound
  · intro a ha
    have huplim := hℓ.const_mul (s : ℝ)
    have hupevent : ∀ᶠ N : ℕ in atTop,
        (s : ℝ) * (Real.log (Nat.lcmUpto N : ℝ) / (N : ℝ)) < a := by
      exact huplim.eventually (by simpa using eventually_lt_nhds ha)
    filter_upwards [hupevent] with N hupp
    have hbound := div_le_div_of_nonneg_right (harmonic_log_den_le_lcm s N)
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    rw [mul_div_assoc] at hbound
    exact hbound.trans_lt hupp

/-- The original actual-harmonic perturbation corollary now needs only the
two external PNT inputs and the perturbation's proved sublinear denominator
condition. The unperturbed baseline is derived, not postulated. -/
theorem harmonic_perturbed_log_den_rate_of_pnt (s : ℕ) (hs : 0 < s)
    (hθ : ThetaPNT) (hℓ : LcmPNT) (r : ℕ → ℚ)
    (hr : Tendsto (fun N => logDen (r N) / (N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N + r N) / (N : ℝ))
      atTop (nhds (s : ℝ)) := by
  exact harmonic_log_den_rate_stability s r (harmonic_log_den_rate_of_pnt s hs hθ hℓ) hr

/-- Positive integral reindexing, including the original `s=9,N=2M`
application. This is still the actual reduced harmonic denominator. -/
theorem harmonic_log_den_rate_nat_scale_of_pnt (s a : ℕ) (hs : 0 < s) (ha : 0 < a)
    (hθ : ThetaPNT) (hℓ : LcmPNT) :
    Tendsto (fun M : ℕ => logDen (harmonicPower s (a * M)) / (M : ℝ))
      atTop (nhds ((s : ℝ) * a)) := by
  have hindex : Tendsto (fun M : ℕ => a * M) atTop atTop := by
    apply tendsto_atTop_mono (fun M => Nat.le_mul_of_pos_left M ha) tendsto_id
  have hbase := ((harmonic_log_den_rate_of_pnt s hs hθ hℓ).comp hindex).mul_const (a : ℝ)
  apply hbase.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  have hMz : (M : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
  have haz : (a : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  dsimp only [Function.comp_def]
  rw [Nat.cast_mul]
  field_simp

/-- The exact denominator rate used by the right-shifted Mellin route. -/
theorem harmonic_nine_double_log_den_rate_of_pnt (hθ : ThetaPNT) (hℓ : LcmPNT) :
    Tendsto (fun M : ℕ => logDen (harmonicPower 9 (2 * M)) / (M : ℝ))
      atTop (nhds 18) := by
  convert harmonic_log_den_rate_nat_scale_of_pnt 9 2 (by decide) (by decide) hθ hℓ using 1
  norm_num









end ZetaNine.HarmonicStability









/-!
# Transfer the actual Chebyshev psi rate to the two harmonic PNT inputs

The existing `ThetaPNT` and `LcmPNT` objects are imported, not redefined.
The transfer theorems identify the actual limit of `Chebyshev.psi x / x`
with the two needed inputs. The unconditional endpoints then derive that
limit from the imported, fully proved original `MediumPNT` theorem and
the decay of its explicit relative exponential error. No PNT axiom or
harmonic denominator-rate premise is introduced.
-/

set_option autoImplicit false
open Filter Asymptotics

namespace ZetaNine.HarmonicStability

/-- The actual Chebyshev difference is negligible after division by x.
This uses Mathlib's proved O(sqrt x) error, and has no PNT premise. -/
theorem psi_theta_normalized_error_tendsto_zero :
    Tendsto (fun x : ℝ => (Chebyshev.psi x - Chebyshev.theta x) / x)
      atTop (nhds 0) := by
  have hsqrt : Tendsto (fun x : ℝ => Real.sqrt x / x) atTop (nhds 0) := by
    simpa only [Real.sqrt_div_self, Function.comp_def] using
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hsqrt_small : IsLittleO atTop Real.sqrt (fun x : ℝ => x) :=
    (isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr hsqrt
  simpa only [Pi.sub_apply] using
    (Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO hsqrt_small).tendsto_div_nhds_zero

/-- The actual psi PNT rate implies the existing theta PNT input. -/
theorem theta_pnt_of_psi_rate
    (hψ : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1)) :
    ThetaPNT := by
  unfold ThetaPNT
  have h := hψ.sub psi_theta_normalized_error_tendsto_zero
  simp only [sub_zero] at h
  convert h using 1
  funext x
  ring

/-- Restricting the actual psi rate to natural endpoints yields the lcm
input by the exact Mathlib identity psi(N)=log(lcmUpto N). -/
theorem lcm_pnt_of_psi_rate
    (hψ : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1)) :
    LcmPNT := by
  unfold LcmPNT
  simpa only [Function.comp_def, Chebyshev.psi_eq_log_lcmUpto] using
    hψ.comp (tendsto_natCast_atTop_atTop (R := ℝ))



/-- The actual harmonic denominator baseline requires only the actual psi
prime-distribution theorem; its denominator growth is derived. -/
theorem harmonic_log_den_rate_of_psi_rate (s : ℕ) (hs : 0 < s)
    (hψ : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1)) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N) / (N : ℝ))
      atTop (nhds (s : ℝ)) :=
  harmonic_log_den_rate_of_pnt s hs (theta_pnt_of_psi_rate hψ) (lcm_pnt_of_psi_rate hψ)

/-- The original double-endpoint order-nine rate, derived from psi alone. -/
theorem harmonic_nine_double_log_den_rate_of_psi_rate
    (hψ : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1)) :
    Tendsto (fun M : ℕ => logDen (harmonicPower 9 (2 * M)) / (M : ℝ))
      atTop (nhds 18) :=
  harmonic_nine_double_log_den_rate_of_pnt (theta_pnt_of_psi_rate hψ) (lcm_pnt_of_psi_rate hψ)

/-- The explicit relative exponential error in the original MediumPNT
theorem tends to zero. Every analytic limit here is proved. -/
theorem medium_pnt_relative_error_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      atTop (nhds 0) := by
  have hpow : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 10)).comp Real.tendsto_log_atTop
  simpa only [Function.comp_def, neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hpow.const_mul_atTop hc)

/-- Convert the actual MediumPNT error estimate to the literal psi PNT
rate. This auxiliary implication introduces no substitute psi function. -/
theorem psi_rate_of_medium_error (c : ℝ) (hc : 0 < c)
    (herror : IsBigO atTop (Chebyshev.psi - id)
      (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))) :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1) := by
  have hweight : Tendsto (fun x : ℝ =>
      (x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) / x) atTop (nhds 0) := by
    apply (medium_pnt_relative_error_tendsto_zero c hc).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    field_simp
  have hsmall : IsLittleO atTop
      (fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)))
      (fun x : ℝ => x) :=
    (isLittleO_iff_tendsto (fun x hx => by simp [hx])).mpr hweight
  have hnormalized : Tendsto (fun x : ℝ => (Chebyshev.psi x - x) / x)
      atTop (nhds 0) := by
    simpa only [Pi.sub_apply, id_eq] using
      (herror.trans_isLittleO hsmall).tendsto_div_nhds_zero
  have hrate := hnormalized.add_const (1 : ℝ)
  simp only [zero_add] at hrate
  apply hrate.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

/-- The actual psi prime-number-theorem rate, derived from the genuine
imported MediumPNT proof and its proved error decay, with no hypotheses. -/
theorem psi_pnt_rate :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (nhds 1) := by
  obtain ⟨c, hc, herror⟩ := MediumPNT
  exact psi_rate_of_medium_error c hc herror

theorem theta_pnt : ThetaPNT := theta_pnt_of_psi_rate psi_pnt_rate

theorem lcm_pnt : LcmPNT := lcm_pnt_of_psi_rate psi_pnt_rate

/-- The original full-sequence harmonic denominator baseline is now
unconditional for every fixed positive order. -/
theorem harmonic_log_den_rate (s : ℕ) (hs : 0 < s) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N) / (N : ℝ))
      atTop (nhds (s : ℝ)) :=
  harmonic_log_den_rate_of_psi_rate s hs psi_pnt_rate

/-- The original rational perturbation corollary, with only its genuine
sublinear perturbation-denominator hypothesis. -/
theorem harmonic_perturbed_log_den_rate (s : ℕ) (hs : 0 < s) (r : ℕ → ℚ)
    (hr : Tendsto (fun N => logDen (r N) / (N : ℝ)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => logDen (harmonicPower s N + r N) / (N : ℝ))
      atTop (nhds (s : ℝ)) :=
  harmonic_perturbed_log_den_rate_of_pnt s hs theta_pnt lcm_pnt r hr

/-- The exact order-nine rate eighteen at double natural endpoints. -/
theorem harmonic_nine_double_log_den_rate :
    Tendsto (fun M : ℕ => logDen (harmonicPower 9 (2 * M)) / (M : ℝ))
      atTop (nhds 18) :=
  harmonic_nine_double_log_den_rate_of_psi_rate psi_pnt_rate















end ZetaNine.HarmonicStability


open ZetaNine.HarmonicStability

theorem solution :
    Tendsto (fun M : ℕ => logDen (harmonicPower 9 (2 * M)) / (M : ℝ))
      atTop (nhds 18) := by
  exact ZetaNine.HarmonicStability.harmonic_nine_double_log_den_rate

#print axioms solution
