-- Prove2me | solution 1 for RamareAnalytic.coefficient_logarithmic_moment
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T21:23:28.329822+00:00
-- url     : https://prove2.me/submissions/0d3b2f89-c911-417f-8725-2a8a62fff9d9

import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator

set_option autoImplicit false

open scoped BigOperators

namespace RamareAnalytic

/-!
Qualitative convergence for the explicit prime-power correction in Ramaré's
harmonic convolution.  This file assumes only multiplicativity and the actual
prime-power values, not convergence or the desired error estimate.

The weighted local Euler factor is bounded by
  1 + 2 * p^(-8/5) + 2 * p^(-6/5).
Both nonconstant terms are summable p-series.  Finite smooth-number Euler
products therefore bound all partial sums of the nonnegative weighted series.
The signed local factor then cancels to one, giving total coefficient mass one.

This is a draft pending an explicitly scheduled compiler check.  It does not
give the quantitative bounds 16 or 67/50 required by the large-range estimate.
-/

/-- A converse convergence criterion obtained from finite smooth-number Euler
products.  The local bound is on the complete prime-power series. -/
theorem summable_of_local_euler_majorant
    (f g : ℕ → ℝ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hf_mul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hlocal : ∀ {p : ℕ}, Nat.Prime p →
      Summable (fun k : ℕ => ‖f (p ^ k)‖))
    (hg_nonneg : ∀ n, 0 ≤ g n) (hg : Summable g)
    (hfactor : ∀ p : ℕ, Nat.Prime p → (∑' k : ℕ, f (p ^ k)) ≤ 1 + g p) :
    Summable f := by
  classical
  apply summable_of_sum_range_le hf_nonneg (c := Real.exp (∑' n : ℕ, g n))
  intro N
  have hs := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
    hf1 hf_mul hlocal N
  have hi : HasSum ((Nat.smoothNumbers N).indicator f)
      (∏ p ∈ Nat.primesBelow N, ∑' k : ℕ, f (p ^ k)) :=
    hasSum_subtype_iff_indicator.mp hs.2
  have hsum : (∑ n ∈ Finset.range N, f n) =
      ∑ n ∈ Finset.range N, (Nat.smoothNumbers N).indicator f n := by
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [Set.indicator_apply, hf0]
    · exact (Set.indicator_of_mem
        (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn0)
          (Finset.mem_range.mp hn)) f).symm
  calc
    (∑ n ∈ Finset.range N, f n) =
        ∑ n ∈ Finset.range N, (Nat.smoothNumbers N).indicator f n := hsum
    _ ≤ ∏ p ∈ Nat.primesBelow N, ∑' k : ℕ, f (p ^ k) := by
      apply sum_le_hasSum _ _ hi
      intro n hn
      by_cases hm : n ∈ Nat.smoothNumbers N
      · simpa only [Set.indicator_of_mem hm] using hf_nonneg n
      · simp only [Set.indicator_of_notMem hm, le_refl]
    _ ≤ ∏ p ∈ Nat.primesBelow N, (1 + g p) := by
      apply Finset.prod_le_prod
      · intro p hp
        exact tsum_nonneg (fun k => hf_nonneg (p ^ k))
      · intro p hp
        exact hfactor p (Nat.mem_primesBelow.mp hp).2
    _ ≤ Real.exp (∑ p ∈ Nat.primesBelow N, g p) :=
      Real.prod_one_add_le_exp_sum _ hg_nonneg
    _ ≤ Real.exp (∑' n : ℕ, g n) := by
      apply Real.exp_le_exp.mpr
      exact hg.sum_le_tsum _ (fun n hn => hg_nonneg n)

private theorem prime_power_tsum_three (f : ℕ → ℝ) (p : ℕ)
    (hz : ∀ k : ℕ, 3 ≤ k → f (p ^ k) = 0) :
    (∑' k : ℕ, f (p ^ k)) = f 1 + f p + f (p ^ 2) := by
  rw [tsum_eq_sum (s := Finset.range 3) (by
    intro k hk
    apply hz k
    simpa only [Finset.mem_range, not_lt] using hk)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]

private theorem power_div_prime_denominator_le (x s : ℝ) (hx : 2 ≤ x) :
    x ^ s / (x * (x - 1)) ≤ 2 * x ^ (s - 2) := by
  have hx0 : 0 < x := by linarith
  have hden : 0 < x * (x - 1) := mul_pos hx0 (by linarith)
  have hrecip : 1 / (x * (x - 1)) ≤ 2 / x ^ 2 := by
    apply (div_le_div_iff₀ hden (sq_pos_of_pos hx0)).mpr
    nlinarith
  calc
    x ^ s / (x * (x - 1)) = x ^ s * (1 / (x * (x - 1))) := by ring
    _ ≤ x ^ s * (2 / x ^ 2) :=
      mul_le_mul_of_nonneg_left hrecip (Real.rpow_nonneg hx0.le _)
    _ = 2 * x ^ (s - 2) := by
      rw [Real.rpow_sub hx0, Real.rpow_two]
      ring

/-- The weighted absolute moment exists for every multiplicative function
with Ramaré's exact prime-power factors. -/
theorem weighted_summable_of_prime_power_values
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) :
    Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) := by
  let f : ℕ → ℝ := fun n => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)
  let g : ℕ → ℝ := fun n =>
    2 * (n : ℝ) ^ (-(8 / 5 : ℝ)) + 2 * (n : ℝ) ^ (-(6 / 5 : ℝ))
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hfz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → f (p ^ k) = 0 := by
    intro p k hp hk
    simp only [f, hpz p k hp hk, abs_zero, zero_mul]
  have hgsum : Summable g := by
    exact ((Real.summable_nat_rpow.mpr (by norm_num : -(8 / 5 : ℝ) < -1)).mul_left 2).add
      ((Real.summable_nat_rpow.mpr (by norm_num : -(6 / 5 : ℝ) < -1)).mul_left 2)
  apply summable_of_local_euler_majorant f g
  · simp [f]
  · simp [f, hmul.1]
  · exact hf_nonneg
  · intro m n hmn
    simp only [f, hmul.2 hmn, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  · intro p hp
    apply summable_of_ne_finset_zero (s := Finset.range 3)
    intro k hk
    have hk3 : 3 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    simp only [hfz p k hp hk3, norm_zero]
  · intro n
    exact add_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · exact hgsum
  · intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hcoef : 0 ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) :=
      div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg p) (by linarith))
    have hsquare : ((p ^ 2 : ℕ) : ℝ) ^ (2 / 5 : ℝ) =
        (p : ℝ) ^ (4 / 5 : ℝ) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
      norm_num
    rw [prime_power_tsum_three f p (fun k hk => hfz p k hp hk)]
    have hform : f 1 + f p + f (p ^ 2) =
        1 + ((p : ℝ) ^ (2 / 5 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) +
          (p : ℝ) ^ (4 / 5 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
      simp only [f, hmul.1, (hpv p hp).1, (hpv p hp).2, Nat.cast_one,
        Real.one_rpow, abs_one, one_mul, abs_neg, abs_of_nonneg hcoef, hsquare]
      ring
    rw [hform]
    have hfirst := power_div_prime_denominator_le (p : ℝ) (2 / 5 : ℝ) hp2
    have hsecond := power_div_prime_denominator_le (p : ℝ) (4 / 5 : ℝ) hp2
    norm_num at hfirst hsecond
    simpa only [g] using add_le_add_right (add_le_add hfirst hsecond) 1

/-- Absolute summability follows from the weighted moment, including the
zero index enforced by `ArithmeticFunction`. -/
theorem norm_summable_of_weighted_summable (h : ArithmeticFunction ℝ)
    (hw : Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ))) :
    Summable (fun n : ℕ => ‖h n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg (h n)) _ hw
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    have hw1 : 1 ≤ (n : ℝ) ^ (2 / 5 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
    simpa only [Real.norm_eq_abs, mul_one] using
      mul_le_mul_of_nonneg_left hw1 (abs_nonneg (h n))

/-- The logarithmic moment is absolutely convergent; the harmless factor 5/2
comes from `log x ≤ x^(2/5)/(2/5)`. -/
theorem log_summable_of_weighted_summable (h : ArithmeticFunction ℝ)
    (hw : Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ))) :
    Summable (fun n : ℕ => h n * Real.log (n : ℝ)) := by
  apply (hw.mul_left (5 / 2 : ℝ)).of_norm_bounded
  intro n
  have hlog : ‖Real.log (n : ℝ)‖ ≤ (n : ℝ) ^ (2 / 5 : ℝ) / (2 / 5 : ℝ) := by
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hn1)]
      exact Real.log_natCast_le_rpow_div n (by norm_num)
  calc
    ‖h n * Real.log (n : ℝ)‖ = |h n| * ‖Real.log (n : ℝ)‖ := by
      rw [norm_mul, Real.norm_eq_abs (h n)]
    _ ≤ |h n| * ((n : ℝ) ^ (2 / 5 : ℝ) / (2 / 5 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog (abs_nonneg (h n))
    _ = (5 / 2 : ℝ) * (|h n| * (n : ℝ) ^ (2 / 5 : ℝ)) := by ring

/-- The signed Euler factors cancel exactly. Convergence is proved from the
prime-power values, so this result assumes no mass or convergence premise. -/
theorem hasSum_one_of_prime_power_values
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) :
    HasSum (fun n : ℕ => h n) 1 := by
  have hw := weighted_summable_of_prime_power_values h hmul hpv hpz
  have hn := norm_summable_of_weighted_summable h hw
  have hfactor : ∀ p : Nat.Primes, (∑' k : ℕ, h ((p : ℕ) ^ k)) = 1 := by
    intro p
    rw [prime_power_tsum_three (fun n => h n) (p : ℕ)
      (fun k hk => hpz (p : ℕ) k p.property hk)]
    rw [hmul.1, (hpv (p : ℕ) p.property).1, (hpv (p : ℕ) p.property).2]
    ring
  have hmass : (∑' n : ℕ, h n) = 1 := by
    rw [← hmul.eulerProduct_tprod hn]
    simp only [hfactor, tprod_one]
  exact hmass ▸ hn.of_norm.hasSum

/-- All qualitative hypotheses of the harmonic-convolution error transfer
follow from the exact coefficient factorization. Quantitative moment bounds
are deliberately separate. -/
theorem moments_of_prime_power_values
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) :
    HasSum (fun n : ℕ => h n) 1 ∧
      Summable (fun n : ℕ => h n * Real.log (n : ℝ)) ∧
      Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) := by
  have hw := weighted_summable_of_prime_power_values h hmul hpv hpz
  exact ⟨hasSum_one_of_prime_power_values h hmul hpv hpz,
    log_summable_of_weighted_summable h hw, hw⟩

end RamareAnalytic

set_option autoImplicit false

open scoped BigOperators Topology
open Filter

namespace RamareAnalytic

/-!
The logarithmic moment of Ramaré's signed correction coefficients.

This draft assumes absolute convergence of h and h(n) log n as explicit
analytic inputs.  These are qualitative consequences of the weighted moment
proved in the separate EulerSummability draft.  No coefficient-moment identity,
prime-series convergence, or quantitative bound is assumed here.

The finite-prime-factor identity is proved first.  Its passage to a HasSum over
primes uses Mathlib's convergence of sums over factored numbers, so it also
proves convergence of the prime series.  There is no differentiation of an
infinite product and no unproved exchange of limits.
-/

private theorem local_prime_mass
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (p : ℕ) (hp : Nat.Prime p)
    (hpv : h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ k : ℕ, 3 ≤ k → h (p ^ k) = 0) :
    HasSum (fun k : ℕ => h (p ^ k)) 1 := by
  have hs := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := Finset.range 3) (f := fun k => h (p ^ k))
    (by
      intro k hk
      exact hpz k (by simpa only [Finset.mem_range, not_lt] using hk))
  have he : (∑ k ∈ Finset.range 3, h (p ^ k)) = 1 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, hmul.1, hpv.1, hpv.2]
    ring
  exact he ▸ hs

private theorem local_prime_log_mass
    (h : ArithmeticFunction ℝ) (p : ℕ) (hp : Nat.Prime p)
    (hpv : h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ k : ℕ, 3 ≤ k → h (p ^ k) = 0) :
    HasSum (fun k : ℕ => h (p ^ k) * Real.log ((p ^ k : ℕ) : ℝ))
      (-(Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))) := by
  have hs := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := Finset.range 3)
    (f := fun k => h (p ^ k) * Real.log ((p ^ k : ℕ) : ℝ)) (by
      intro k hk
      rw [hpz k (by simpa only [Finset.mem_range, not_lt] using hk), zero_mul])
  have he : (∑ k ∈ Finset.range 3, h (p ^ k) * Real.log ((p ^ k : ℕ) : ℝ)) =
      -(Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, hpv.1, hpv.2, Nat.cast_one, Real.log_one, mul_zero,
      Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    ring
  exact he ▸ hs

/-- Restricting to any finite set of allowed prime factors preserves signed
mass one. This does not identify a finite cutoff with a smooth-number set. -/
private theorem factored_mass_one
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0)
    (hnorm : Summable (fun n : ℕ => ‖h n‖)) (s : Finset ℕ) :
    HasSum (fun m : Nat.factoredNumbers s => h (m : ℕ)) 1 := by
  have hs := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hmul.1 hmul.2
    (fun hp => hnorm.comp_injective (Nat.pow_right_injective hp.one_lt)) s).2
  have he : (∏ p ∈ s with p.Prime, ∑' k : ℕ, h (p ^ k)) = 1 := by
    apply Finset.prod_eq_one
    intro p hp
    have hpp := (Finset.mem_filter.mp hp).2
    exact (local_prime_mass h hmul p hpp (hpv p hpp)
      (fun k hk => hpz p k hpp hk)).tsum_eq
  exact he ▸ hs

/- Finite Euler differentiation without differentiating: adjoining a new
prime adds its local logarithmic moment because both signed masses are one. -/
set_option maxHeartbeats 800000 in
theorem factored_logarithmic_moment
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0)
    (hnorm : Summable (fun n : ℕ => ‖h n‖))
    (hlognorm : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)‖))
    (s : Finset ℕ) :
    HasSum (fun m : Nat.factoredNumbers s => h (m : ℕ) * Real.log (m : ℝ))
      (-(∑ p ∈ s with p.Prime,
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Nat.factoredNumbers_empty]
    simp only [Finset.filter_empty, Finset.sum_empty, neg_zero]
    have hz : HasSum (fun _ : ({1} : Set ℕ) => (0 : ℝ)) 0 := hasSum_zero
    apply hz.congr_fun
    intro m
    have hm : (m : ℕ) = 1 := Set.mem_singleton_iff.mp m.property
    simp only [hm, Nat.cast_one, Real.log_one, mul_zero]
  | @insert p s hps ih =>
    by_cases hp : p.Prime
    · have hpfilter : p ∉ {q ∈ s | q.Prime} := by
        intro hh
        exact hps (Finset.mem_filter.mp hh).1
      rw [Finset.filter_insert, if_pos hp, Finset.sum_insert hpfilter,
        ← (Nat.equivProdNatFactoredNumbers hp hps).hasSum_iff, Function.comp_def]
      have hnp : Summable (fun k : ℕ => ‖h (p ^ k)‖) :=
        hnorm.comp_injective (Nat.pow_right_injective hp.one_lt)
      have hlp : Summable (fun k : ℕ => ‖h (p ^ k) * Real.log ((p ^ k : ℕ) : ℝ)‖) :=
        hlognorm.comp_injective (Nat.pow_right_injective hp.one_lt)
      have hns : Summable (fun m : Nat.factoredNumbers s => ‖h (m : ℕ)‖) :=
        hnorm.subtype (Nat.factoredNumbers s)
      have hls : Summable (fun m : Nat.factoredNumbers s =>
          ‖h (m : ℕ) * Real.log (m : ℝ)‖) :=
        hlognorm.subtype (Nat.factoredNumbers s)
      have hprod_left : Summable (fun x : ℕ × Nat.factoredNumbers s =>
          (h (p ^ x.1) * Real.log ((p ^ x.1 : ℕ) : ℝ)) * h (x.2 : ℕ)) :=
        summable_mul_of_summable_norm hlp hns
      have hprod_right : Summable (fun x : ℕ × Nat.factoredNumbers s =>
          h (p ^ x.1) * (h (x.2 : ℕ) * Real.log (x.2 : ℝ))) :=
        summable_mul_of_summable_norm hnp hls
      have hleft := (local_prime_log_mass h p hp (hpv p hp)
        (fun k hk => hpz p k hp hk)).mul
          (factored_mass_one h hmul hpv hpz hnorm s)
          hprod_left
      have hright := (local_prime_mass h hmul p hp (hpv p hp)
        (fun k hk => hpz p k hp hk)).mul ih
          hprod_right
      have hjoined := hleft.add hright
      simp only [mul_one, one_mul, ← neg_add] at hjoined
      apply hjoined.congr_fun
      intro x
      rw [Nat.equivProdNatFactoredNumbers_apply',
        Nat.factoredNumbers.map_prime_pow_mul hmul.2 hp hps,
        Nat.cast_mul, Real.log_mul]
      · ring
      · exact Nat.cast_ne_zero.mpr (pow_ne_zero x.1 hp.ne_zero)
      · exact Nat.cast_ne_zero.mpr (Nat.ne_zero_of_mem_factoredNumbers x.2.property)
    · rw [Nat.factoredNumbers_insert s hp, Finset.filter_insert, if_neg hp]
      exact ih

/-- The prime logarithmic series has the negative coefficient log moment as
its sum. Its convergence is a conclusion, not a premise. -/
theorem prime_log_hasSum_neg_coefficient_moment
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0)
    (hnorm : Summable (fun n : ℕ => ‖h n‖))
    (hlognorm : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)‖)) :
    HasSum (fun p : Nat.Primes =>
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))
      (-(∑' n : ℕ, h n * Real.log (n : ℝ))) := by
  classical
  let g : ℕ → ℝ := fun p => Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
  change HasSum (g ∘ Subtype.val (p := (· ∈ {p | Nat.Prime p}))) _
  rw [hasSum_subtype_iff_indicator]
  change Tendsto
    (fun s : Finset ℕ => ∑ p ∈ s, Set.indicator {p | Nat.Prime p} g p)
    atTop (𝓝 (-(∑' n : ℕ, h n * Real.log (n : ℝ))))
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := EulerProduct.norm_tsum_factoredNumbers_sub_tsum_lt
    hlognorm.of_norm (by simp) hε
  refine ⟨Finset.range N, fun s hs => ?_⟩
  have hfilter : (∑ p ∈ s, Set.indicator {p | Nat.Prime p} g p) =
      ∑ p ∈ s with p.Prime, g p :=
    Finset.sum_indicator_eq_sum_filter s (fun _ => g) _ id
  have hfinite := (factored_logarithmic_moment h hmul hpv hpz hnorm hlognorm s).tsum_eq
  have hdiff : (∑ p ∈ s with p.Prime, g p) -
        (-(∑' n : ℕ, h n * Real.log (n : ℝ))) =
      (∑' n : ℕ, h n * Real.log (n : ℝ)) -
        (∑' m : Nat.factoredNumbers s, h (m : ℕ) * Real.log (m : ℝ)) := by
    rw [hfinite]
    dsimp only [g]
    ring
  rw [hfilter, dist_eq_norm, hdiff]
  apply hN s
  intro p hp
  exact hs (Finset.mem_range.mpr (Nat.lt_of_mem_primesBelow hp))

theorem logarithmic_moment_identity
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0)
    (hnorm : Summable (fun n : ℕ => ‖h n‖))
    (hlognorm : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)‖)) :
    -(∑' n : ℕ, h n * Real.log (n : ℝ)) =
      ∑' p : Nat.Primes, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) :=
  (prime_log_hasSum_neg_coefficient_moment h hmul hpv hpz hnorm hlognorm).tsum_eq.symm

end RamareAnalytic

theorem solution
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))))
    (hpz : ∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) :
    HasSum (fun p : Nat.Primes =>
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))
      (-(∑' n : ℕ, h n * Real.log (n : ℝ))) := by
  have hm := RamareAnalytic.moments_of_prime_power_values h hmul hpv hpz
  exact RamareAnalytic.prime_log_hasSum_neg_coefficient_moment h hmul hpv hpz
    (RamareAnalytic.norm_summable_of_weighted_summable h hm.2.2) hm.2.1.norm

#print axioms solution
