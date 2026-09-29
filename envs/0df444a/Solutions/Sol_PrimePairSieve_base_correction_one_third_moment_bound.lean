-- Prove2me | solution 1 for PrimePairSieve.base_correction_one_third_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T01:34:06.966987+00:00
-- url     : https://prove2.me/submissions/ea1354fd-e243-4287-9b2e-efd7bcd82281

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
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds



set_option autoImplicit false
open scoped BigOperators

namespace PrimePairConvolution

/-- Reused checked generic smooth-number Euler-product criterion. -/
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

/-!
Qualitative convergence for the actual cubic correction of the base-shift-two
Selberg coefficient. Hypotheses are exactly its multiplicativity and published
prime-power values. There is no convergence, coefficient-mass, or numerical
moment hypothesis. In particular the older Ramaré bound 16 is not used.

The standalone generator prepends the already checked generic smooth-number
Euler-majorant criterion from discovery_ramare_large/EulerSummability.lean.
-/

private theorem cubic_prime_power_tsum (f : ℕ → ℝ) (p : ℕ)
    (hz : ∀ k : ℕ, 4 ≤ k → f (p ^ k) = 0) :
    (∑' k : ℕ, f (p ^ k)) = f 1 + f p + f (p ^ 2) + f (p ^ 3) := by
  rw [tsum_eq_sum (s := Finset.range 4) (by
    intro k hk
    apply hz k
    simpa only [Finset.mem_range, not_lt] using hk)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]

private theorem odd_cubic_local_abs_bounds (x : ℝ) (hx : 3 ≤ x) :
    |2 / (x - 2) - 2 / x| ≤ 12 / x^2 ∧
    |1 / x^2 - 2 * (2 / (x - 2)) / x| ≤ 11 / x^2 ∧
    |(2 / (x - 2)) / x^2| ≤ 6 / x^3 := by
  have hx0 : 0 < x := by linarith
  have hx2 : 0 < x - 2 := by linarith
  have hfirst : 2 / (x - 2) - 2 / x = 4 / (x * (x - 2)) := by
    field_simp [hx0.ne', hx2.ne'] <;> ring
  have hsecond : 1 / x^2 - 2 * (2 / (x - 2)) / x =
      -((3 * x + 2) / (x^2 * (x - 2))) := by
    field_simp [hx0.ne', hx2.ne'] <;> ring
  have hthird : (2 / (x - 2)) / x^2 = 2 / (x^2 * (x - 2)) := by
    field_simp [hx0.ne', hx2.ne'] <;> ring
  rw [hfirst, hsecond, hthird, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 4 / (x * (x - 2))),
    abs_of_nonneg (by positivity : 0 ≤ (3 * x + 2) / (x^2 * (x - 2))),
    abs_of_nonneg (by positivity : 0 ≤ 2 / (x^2 * (x - 2)))]
  refine ⟨?_, ?_, ?_⟩
  · apply (div_le_div_iff₀ (by positivity : 0 < x * (x - 2))
      (by positivity : 0 < x^2)).mpr
    nlinarith [mul_nonneg hx0.le (sub_nonneg.mpr hx)]
  · apply (div_le_div_iff₀ (by positivity : 0 < x^2 * (x - 2))
      (by positivity : 0 < x^2)).mpr
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx)]
  · apply (div_le_div_iff₀ (by positivity : 0 < x^2 * (x - 2))
      (by positivity : 0 < x^3)).mpr
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hx)]

/-- Coarse absolute bounds valid also at the exceptional prime two. -/
theorem cubic_prime_absolute_bounds (h : ArithmeticFunction ℝ)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (p : ℕ) (hp : p.Prime) :
    |h p| ≤ 12 / (p : ℝ)^2 ∧
    |h (p^2)| ≤ 11 / (p : ℝ)^2 ∧
    |h (p^3)| ≤ 6 / (p : ℝ)^3 := by
  rcases hpv p hp with ⟨hfirst, hsecond, hthird⟩
  rw [hfirst, hsecond, hthird]
  by_cases hp2 : p = 2
  · subst p
    norm_num
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    simpa only [if_neg hp2] using
      odd_cubic_local_abs_bounds (p : ℝ) (by exact_mod_cast hp3)

private theorem weighted_ratio (c x s : ℝ) (j : ℕ) (hx : 0 < x) :
    (c / x^j) * x^s = c * x^(s - (j : ℝ)) := by
  rw [Real.rpow_sub hx, Real.rpow_natCast]
  ring

/-- Absolute summability with the positive weight n^(2/5), derived from the
actual cubic local coefficients. This assumes no Euler-product convergence. -/
theorem weighted_summable_of_cubic_prime_power_values
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) := by
  let f : ℕ → ℝ := fun n => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)
  let g : ℕ → ℝ := fun n =>
    12 * (n : ℝ)^(-(8 / 5 : ℝ)) + 11 * (n : ℝ)^(-(6 / 5 : ℝ)) +
      6 * (n : ℝ)^(-(9 / 5 : ℝ))
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hfz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → f (p ^ k) = 0 := by
    intro p k hp hk
    simp only [f, hpz p k hp hk, abs_zero, zero_mul]
  have hgsum : Summable g := by
    exact (((Real.summable_nat_rpow.mpr
        (by norm_num : -(8 / 5 : ℝ) < -1)).mul_left 12).add
      ((Real.summable_nat_rpow.mpr
        (by norm_num : -(6 / 5 : ℝ) < -1)).mul_left 11)).add
      ((Real.summable_nat_rpow.mpr
        (by norm_num : -(9 / 5 : ℝ) < -1)).mul_left 6)
  apply summable_of_local_euler_majorant f g
  · simp [f]
  · simp [f, hmul.1]
  · exact hf_nonneg
  · intro m n hmn
    simp only [f, hmul.2 hmn, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  · intro p hp
    apply summable_of_ne_finset_zero (s := Finset.range 4)
    intro k hk
    have hk4 : 4 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
    simp only [hfz p k hp hk4, norm_zero]
  · intro n
    exact add_nonneg (add_nonneg
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · exact hgsum
  · intro p hp
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hb := cubic_prime_absolute_bounds h hpv p hp
    have hsquare : ((p^2 : ℕ) : ℝ)^(2 / 5 : ℝ) = (p : ℝ)^(4 / 5 : ℝ) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
      norm_num
    have hcube : ((p^3 : ℕ) : ℝ)^(2 / 5 : ℝ) = (p : ℝ)^(6 / 5 : ℝ) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
      norm_num
    have hfirst : f p ≤ 12 * (p : ℝ)^(-(8 / 5 : ℝ)) := by
      calc
        _ ≤ (12 / (p : ℝ)^2) * (p : ℝ)^(2 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_right hb.1 (Real.rpow_nonneg hp0.le _)
        _ = _ := by
          convert weighted_ratio 12 (p : ℝ) (2 / 5 : ℝ) 2 hp0 using 1 <;> norm_num
    have hsecond : f (p^2) ≤ 11 * (p : ℝ)^(-(6 / 5 : ℝ)) := by
      change |h (p^2)| * ((p^2 : ℕ) : ℝ)^(2 / 5 : ℝ) ≤ _
      rw [hsquare]
      calc
        _ ≤ (11 / (p : ℝ)^2) * (p : ℝ)^(4 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_right hb.2.1 (Real.rpow_nonneg hp0.le _)
        _ = _ := by
          convert weighted_ratio 11 (p : ℝ) (4 / 5 : ℝ) 2 hp0 using 1 <;> norm_num
    have hthird : f (p^3) ≤ 6 * (p : ℝ)^(-(9 / 5 : ℝ)) := by
      change |h (p^3)| * ((p^3 : ℕ) : ℝ)^(2 / 5 : ℝ) ≤ _
      rw [hcube]
      calc
        _ ≤ (6 / (p : ℝ)^3) * (p : ℝ)^(6 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_right hb.2.2 (Real.rpow_nonneg hp0.le _)
        _ = _ := by
          convert weighted_ratio 6 (p : ℝ) (6 / 5 : ℝ) 3 hp0 using 1 <;> norm_num
    rw [cubic_prime_power_tsum f p (fun k hk => hfz p k hp hk)]
    have hf1 : f 1 = 1 := by simp [f, hmul.1]
    rw [hf1]
    dsimp only [g]
    linarith


end PrimePairConvolution



/-!
The actual cubic coefficient's one-third weighted moment and Euler products.
Convergence is derived from the checked two-fifths convergence theorem. The
finite-product numerical bound is a separate internal assembly interface.
-/

open scoped BigOperators Topology
open Filter

namespace PrimePairConvolution

noncomputable def cubicWeightedEulerFactor (p : ℕ) : ℝ :=
  if p=2 then 3/2+(3/4 : ℝ)*(2 : ℝ)^(2/3 : ℝ)
  else 1+4*(p : ℝ)^(1/3 : ℝ)/((p : ℝ)*((p : ℝ)-2))+
    (3*(p : ℝ)+2)*(p : ℝ)^(2/3 : ℝ)/((p : ℝ)^2*((p : ℝ)-2))+
    2/((p : ℝ)*((p : ℝ)-2))

theorem weighted_oneThird_summable_of_cubic_prime_power_values
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    Summable (fun n : ℕ => |h n| * (n : ℝ)^(1 / 3 : ℝ)) := by
  have htwo := weighted_summable_of_cubic_prime_power_values h hmul hpv hpz
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ htwo
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1 / 3 : ℝ) ≤ 2 / 5))
      (abs_nonneg _)

/-- The local absolute factor, including the exceptional prime two. -/
theorem cubic_weighted_prime_factor
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0)
    (p : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, |h (p ^ k)| * ((p ^ k : ℕ) : ℝ)^(1 / 3 : ℝ)) =
      cubicWeightedEulerFactor p := by
  let f : ℕ → ℝ := fun n => |h n| * (n : ℝ)^(1 / 3 : ℝ)
  change (∑' k : ℕ, f (p ^ k)) = _
  have hz : ∀ k : ℕ, 4 ≤ k → f (p ^ k) = 0 := by
    intro k hk
    simp only [f, hpz p k hp hk, abs_zero, zero_mul]
  have hfour : (∑' k : ℕ, f (p ^ k)) = f 1 + f p + f (p ^ 2) + f (p ^ 3) := by
    rw [tsum_eq_sum (s := Finset.range 4) (by
      intro k hk
      apply hz k
      simpa only [Finset.mem_range, not_lt] using hk)]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one]
  have hsquare : ((p ^ 2 : ℕ) : ℝ)^(1 / 3 : ℝ) = (p : ℝ)^(2 / 3 : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
    norm_num
  have hcube : ((p ^ 3 : ℕ) : ℝ)^(1 / 3 : ℝ) = (p : ℝ) := by
    rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p)]
    norm_num
  rw [hfour]
  simp only [f, hmul.1, Nat.cast_one, Real.one_rpow, abs_one, one_mul,
    hsquare, hcube]
  by_cases hp2 : p = 2
  · subst p
    have hvals := hpv 2 Nat.prime_two
    norm_num at hvals
    norm_num [cubicWeightedEulerFactor, hvals.1, hvals.2.1, hvals.2.2] <;> ring
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hp0 : 0 < (p : ℝ) := by linarith
    have hpden : 0 < (p : ℝ) - 2 := by linarith
    have hfirst : h p = 4 / ((p : ℝ) * ((p : ℝ) - 2)) := by
      rw [(hpv p hp).1, if_neg hp2]
      field_simp [hp0.ne', hpden.ne'] <;> ring
    have hsecond : h (p^2) = -((3 * (p : ℝ) + 2) / ((p : ℝ)^2 * ((p : ℝ) - 2))) := by
      rw [(hpv p hp).2.1, if_neg hp2]
      field_simp [hp0.ne', hpden.ne'] <;> ring
    have hthird : h (p^3) = 2 / ((p : ℝ)^2 * ((p : ℝ) - 2)) := by
      rw [(hpv p hp).2.2, if_neg hp2]
      field_simp [hp0.ne', hpden.ne'] <;> ring
    rw [hfirst, hsecond, hthird, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ 4 / ((p : ℝ) * ((p : ℝ) - 2))),
      abs_of_nonneg (by positivity : 0 ≤ (3 * (p : ℝ) + 2) / ((p : ℝ)^2 * ((p : ℝ) - 2))),
      abs_of_nonneg (by positivity : 0 ≤ 2 / ((p : ℝ)^2 * ((p : ℝ) - 2)))]
    simp only [cubicWeightedEulerFactor, if_neg hp2]
    field_simp [hp0.ne', hpden.ne'] <;> ring

theorem cubicWeightedEulerFactor_one_le (p : ℕ) (hp : p.Prime) :
    1 ≤ cubicWeightedEulerFactor p := by
  by_cases hp2 : p = 2
  · subst p
    have hpow := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 / 3 : ℝ)
    change (1 : ℝ) ≤ 3 / 2 + (3 / 4 : ℝ) * (2 : ℝ)^(2 / 3 : ℝ)
    nlinarith
  · have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have hp0 : 0 < (p : ℝ) := by linarith
    have hpden : 0 < (p : ℝ) - 2 := by linarith
    have h1 : 0 ≤ 4*(p : ℝ)^(1/3 : ℝ)/((p : ℝ)*((p : ℝ)-2)) := by positivity
    have h2 : 0 ≤ (3*(p : ℝ)+2)*(p : ℝ)^(2/3 : ℝ)/((p : ℝ)^2*((p : ℝ)-2)) := by positivity
    have h3 : 0 ≤ 2/((p : ℝ)*((p : ℝ)-2)) := by positivity
    simp only [cubicWeightedEulerFactor, if_neg hp2]
    linarith

/-- Actual finite cubic Euler products converge to the actual one-third moment.
No convergence or numerical bound is an input hypothesis. -/
theorem cubic_weighted_euler_limit
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N,
      if p=2 then 3/2+(3/4 : ℝ)*(2 : ℝ)^(2/3 : ℝ)
      else 1+4*(p : ℝ)^(1/3 : ℝ)/((p : ℝ)*((p : ℝ)-2))+
        (3*(p : ℝ)+2)*(p : ℝ)^(2/3 : ℝ)/((p : ℝ)^2*((p : ℝ)-2))+
        2/((p : ℝ)*((p : ℝ)-2))) atTop
      (𝓝 (∑' n : ℕ, |h n| * (n : ℝ)^(1 / 3 : ℝ))) := by
  let f : ℕ → ℝ := fun n => |h n| * (n : ℝ)^(1 / 3 : ℝ)
  have hf0 : f 0 = 0 := by simp [f]
  have hf1 : f 1 = 1 := by simp [f, hmul.1]
  have hf_nonneg : ∀ n : ℕ, 0 ≤ f n := by
    intro n
    exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hf_mul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [f, hmul.2 hmn, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
    ring
  have hfSum : Summable f :=
    weighted_oneThird_summable_of_cubic_prime_power_values h hmul hpv hpz
  have hfNorm : Summable (fun n : ℕ => ‖f n‖) :=
    hfSum.congr (fun n => (Real.norm_of_nonneg (hf_nonneg n)).symm)
  have hEuler := EulerProduct.eulerProduct hf1 hf_mul hfNorm hf0
  have hproducts : (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, ∑' k : ℕ, f (p ^ k)) =
      (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, cubicWeightedEulerFactor p) := by
    funext N
    apply Finset.prod_congr rfl
    intro p hp
    exact cubic_weighted_prime_factor h hmul hpv hpz p (Nat.mem_primesBelow.mp hp).2
  rw [hproducts] at hEuler
  exact hEuler

/-- Internal limit transport for the later finite/tail certificate assembly. -/
theorem cubic_weighted_moment_le_of_product_bound
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0)
    (M : ℝ) (hproducts : ∀ N : ℕ,
      (∏ p ∈ Nat.primesBelow N, cubicWeightedEulerFactor p) ≤ M) :
    (∑' n : ℕ, |h n| * (n : ℝ)^(1 / 3 : ℝ)) ≤ M := by
  exact le_of_tendsto' (cubic_weighted_euler_limit h hmul hpv hpz) hproducts

end PrimePairConvolution




set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace PrimePairFiniteConstants

/-!
Finite absolute Euler factors of the actual cubic correction at exponent1/3.
The rounded-product checker pattern follows the checked local Ramaré component
FinitePrimeProduct.lean, with new cubic factors, data, and exact root bounds.
No infinite Euler-product or moment estimate is assumed here.
-/

private structure CubicProductRow where
  prime : ℕ
  rootUpper : ℕ
  after : ℕ
  deriving DecidableEq

private def rootScale : ℕ := 10000
private def roundScale : ℕ := 100000000
private def denominator (p : ℕ) : ℕ := p^2*(p-2)

/-- A total nonnegative extension of the actual local factor. The natural
subtraction is converted to the real denominator on every prime at the end. -/
noncomputable def cubicWeightedFactor (p : ℕ) : ℝ :=
  if p=2 then 3/2+(3/4 : ℝ)*(p : ℝ)^(2/3 : ℝ)
  else 1+(4*(p : ℝ)*(p : ℝ)^(1/3 : ℝ)+
    (3*(p : ℝ)+2)*(p : ℝ)^(2/3 : ℝ)+2*(p : ℝ))/(denominator p : ℝ)

private theorem factor_one_le (p : ℕ) : 1 ≤ cubicWeightedFactor p := by
  unfold cubicWeightedFactor
  split_ifs
  · have h := Real.rpow_nonneg (Nat.cast_nonneg p) (2/3 : ℝ)
    linarith
  · exact le_add_of_nonneg_right (by positivity)

private theorem factor_nonneg (p : ℕ) : 0 ≤ cubicWeightedFactor p :=
  le_trans (by norm_num) (factor_one_le p)

private def upperNum (p u : ℕ) : ℕ :=
  if p=2 then 6*rootScale^2+3*u^2
  else denominator p*rootScale^2+4*p*u*rootScale+(3*p+2)*u^2+2*p*rootScale^2

private def upperDen (p : ℕ) : ℕ :=
  if p=2 then 4*rootScale^2 else denominator p*rootScale^2

private theorem root_upper (p u : ℕ)
    (h : p*rootScale^3 ≤ u^3) :
    (p : ℝ)^(1/3 : ℝ) ≤ (u : ℝ)/(rootScale : ℝ) := by
  have hD : (0 : ℝ)<(rootScale : ℝ) := by norm_num [rootScale]
  have hc : ((p : ℝ)^(1/3 : ℝ))^3=(p : ℝ) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
    norm_num
  apply (pow_le_pow_iff_left₀ (Real.rpow_nonneg (Nat.cast_nonneg p) _)
    (div_nonneg (Nat.cast_nonneg u) hD.le) (by decide : (3 : ℕ)≠0)).mp
  rw [hc,div_pow]
  apply (le_div_iff₀ (pow_pos hD 3)).mpr
  exact_mod_cast h

private theorem denominator_pos (p : ℕ) (hp : 3≤p) : 0<denominator p := by
  unfold denominator
  exact Nat.mul_pos (pow_pos (by omega) 2) (by omega)

private theorem upperDen_pos (p : ℕ) (hp : 2≤p) : 0<upperDen p := by
  unfold upperDen
  split_ifs with h
  · norm_num [rootScale]
  · exact Nat.mul_pos (denominator_pos p (by omega)) (by norm_num [rootScale])

private theorem factor_upper (p u : ℕ) (hp : 2≤p)
    (h : p*rootScale^3 ≤ u^3) :
    cubicWeightedFactor p ≤ (upperNum p u : ℝ)/(upperDen p : ℝ) := by
  have hD : (0 : ℝ)<(rootScale : ℝ) := by norm_num [rootScale]
  have ht := root_upper p u h
  have hs : (p : ℝ)^(2/3 : ℝ) ≤ ((u : ℝ)/(rootScale : ℝ))^2 := by
    have hid : (p : ℝ)^(2/3 : ℝ)=((p : ℝ)^(1/3 : ℝ))^2 := by
      rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      norm_num
    rw [hid]
    exact pow_le_pow_left₀ (Real.rpow_nonneg (Nat.cast_nonneg p) _) ht 2
  by_cases hp2 : p=2
  · calc
      _ = 3/2+(3/4 : ℝ)*(p : ℝ)^(2/3 : ℝ) := by simp only [cubicWeightedFactor,hp2,if_true]
      _ ≤ 3/2+(3/4 : ℝ)*((u : ℝ)/(rootScale : ℝ))^2 := by linarith
      _ = _ := by
        simp only [upperNum,upperDen,hp2,if_true]
        push_cast
        field_simp [hD.ne'] <;> ring
  · have hp3 : 3≤p := by omega
    have hden : (0 : ℝ)<(denominator p : ℝ) := by exact_mod_cast denominator_pos p hp3
    have h1 := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ)≤4*(p : ℝ))
    have h2 := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ)≤3*(p : ℝ)+2)
    have hnum :
        4*(p : ℝ)*(p : ℝ)^(1/3 : ℝ)+(3*(p : ℝ)+2)*(p : ℝ)^(2/3 : ℝ)+2*(p : ℝ) ≤
        4*(p : ℝ)*((u : ℝ)/(rootScale : ℝ))+
          (3*(p : ℝ)+2)*((u : ℝ)/(rootScale : ℝ))^2+2*(p : ℝ) := by linarith
    calc
      _ ≤ 1+(4*(p : ℝ)*((u : ℝ)/(rootScale : ℝ))+
          (3*(p : ℝ)+2)*((u : ℝ)/(rootScale : ℝ))^2+2*(p : ℝ))/(denominator p : ℝ) := by
        simp only [cubicWeightedFactor,hp2,if_false]
        have hd := div_le_div_of_nonneg_right hnum hden.le
        linarith
      _ = _ := by
        simp only [upperNum,upperDen,hp2,if_false]
        push_cast
        field_simp [hD.ne',hden.ne'] <;> ring

private theorem rounded_step (a p u b : ℕ) (hp : 2≤p)
    (hroot : p*rootScale^3≤u^3)
    (hstep : a*upperNum p u≤b*upperDen p) :
    (a : ℝ)/(roundScale : ℝ)*cubicWeightedFactor p ≤ (b : ℝ)/(roundScale : ℝ) := by
  have hR : (0 : ℝ)<(roundScale : ℝ) := by norm_num [roundScale]
  have hden : (0 : ℝ)<(upperDen p : ℝ) := by exact_mod_cast upperDen_pos p hp
  have hstepR : (a : ℝ)*(upperNum p u : ℝ)≤(b : ℝ)*(upperDen p : ℝ) := by
    exact_mod_cast hstep
  calc
    _ ≤ (a : ℝ)/(roundScale : ℝ)*((upperNum p u : ℝ)/(upperDen p : ℝ)) :=
      mul_le_mul_of_nonneg_left (factor_upper p u hp hroot) (by positivity)
    _ ≤ _ := by
      rw [div_mul_div_comm]
      apply (div_le_div_iff₀ (mul_pos hR hden) hR).mpr
      nlinarith [mul_le_mul_of_nonneg_right hstepR hR.le]

private def productCheck (a : ℕ) : List CubicProductRow → Bool
  | [] => decide (a≤22700000000)
  | r::rs => decide (2≤r.prime ∧ r.prime*rootScale^3≤r.rootUpper^3 ∧
      a*upperNum r.prime r.rootUpper≤r.after*upperDen r.prime) && productCheck r.after rs

private theorem factor_list_nonneg (rs : List CubicProductRow) :
    0≤(rs.map (fun r=>cubicWeightedFactor r.prime)).prod := by
  apply List.prod_nonneg
  intro x hx
  obtain ⟨r,_,rfl⟩:=List.mem_map.mp hx
  exact factor_nonneg r.prime

private theorem productCheck_sound (rs : List CubicProductRow) :
    ∀ a, productCheck a rs=true →
      (a : ℝ)/(roundScale : ℝ)*(rs.map (fun r=>cubicWeightedFactor r.prime)).prod≤227 := by
  induction rs with
  | nil =>
    intro a h
    have ha : a≤22700000000 := of_decide_eq_true h
    have har : (a : ℝ)≤22700000000 := by exact_mod_cast ha
    simp only [List.map_nil,List.prod_nil,mul_one]
    calc
      _ ≤ 22700000000/(roundScale : ℝ) := div_le_div_of_nonneg_right har (Nat.cast_nonneg _)
      _ = _ := by norm_num [roundScale]
  | cons r rs ih =>
    intro a h
    have hparts:=Bool.and_eq_true_iff.mp h
    have hrow : 2≤r.prime ∧ r.prime*rootScale^3≤r.rootUpper^3 ∧
        a*upperNum r.prime r.rootUpper≤r.after*upperDen r.prime := of_decide_eq_true hparts.1
    have hstep:=rounded_step a r.prime r.rootUpper r.after hrow.1 hrow.2.1 hrow.2.2
    have htail:=ih r.after hparts.2
    simp only [List.map_cons,List.prod_cons]
    calc
      _ = ((a : ℝ)/(roundScale : ℝ)*cubicWeightedFactor r.prime)*
          (rs.map (fun r=>cubicWeightedFactor r.prime)).prod := by ring
      _ ≤ ((r.after : ℝ)/(roundScale : ℝ))*
          (rs.map (fun r=>cubicWeightedFactor r.prime)).prod :=
        mul_le_mul_of_nonneg_right hstep (factor_list_nonneg rs)
      _ ≤ 227 := htail

-- Literal prime, cube-root numerator, and rounded-product numerator rows.
private def rows : List CubicProductRow :=
  [
    ⟨2, 12600, 269070000⟩,
    ⟨3, 14423, 1650000687⟩,
    ⟨5, 17100, 3716014948⟩,
    ⟨7, 19130, 6017427746⟩,
    ⟨11, 22240, 7636287989⟩,
    ⟨13, 23514, 9176547242⟩,
    ⟨17, 25713, 10360422039⟩,
    ⟨19, 26685, 11476212048⟩,
    ⟨23, 28439, 12387232864⟩,
    ⟨29, 30724, 13071608260⟩,
    ⟨31, 31414, 13723116009⟩,
    ⟨37, 33323, 14244934562⟩,
    ⟨41, 34483, 14708590313⟩,
    ⟨43, 35034, 15154152222⟩,
    ⟨47, 36089, 15555843279⟩,
    ⟨53, 37563, 15900494779⟩,
    ⟨59, 38930, 16200973427⟩,
    ⟨61, 39365, 16492411624⟩,
    ⟨67, 40616, 16750793823⟩,
    ⟨71, 41409, 16991807534⟩,
    ⟨73, 41794, 17226533510⟩,
    ⟨79, 42909, 17438545300⟩,
    ⟨83, 43621, 17638248557⟩,
    ⟨89, 44648, 17820737075⟩,
    ⟨97, 45948, 17983475435⟩,
    ⟨101, 46571, 18138371122⟩,
    ⟨103, 46876, 18290232430⟩,
    ⟨107, 47475, 18435166534⟩,
    ⟨109, 47769, 18577397905⟩,
    ⟨113, 48346, 18713469472⟩,
    ⟨127, 50266, 18829350848⟩,
    ⟨131, 50788, 18940875819⟩,
    ⟨137, 51552, 19046089628⟩,
    ⟨139, 51802, 19149716762⟩,
    ⟨149, 53015, 19244054203⟩,
    ⟨151, 53251, 19337067892⟩,
    ⟨157, 53947, 19425475600⟩,
    ⟨163, 54626, 19509665145⟩,
    ⟨167, 55069, 19591349170⟩,
    ⟨173, 55721, 19669357108⟩,
    ⟨179, 56358, 19743969928⟩,
    ⟨181, 56567, 19817692249⟩,
    ⟨191, 57590, 19886249932⟩,
    ⟨193, 57790, 19954034950⟩,
    ⟨197, 58187, 20020101863⟩,
    ⟨199, 58383, 20085444626⟩,
    ⟨211, 59534, 20145783612⟩,
    ⟨223, 60642, 20201749420⟩,
    ⟨227, 61002, 20256477466⟩,
    ⟨229, 61181, 20310678440⟩,
    ⟨233, 61535, 20363711079⟩,
    ⟨239, 62059, 20415007898⟩,
    ⟨241, 62231, 20465831768⟩,
    ⟨251, 63080, 20513942519⟩,
    ⟨257, 63579, 20560587551⟩,
    ⟨263, 64070, 20605843163⟩,
    ⟨269, 64554, 20649780950⟩,
    ⟨271, 64713, 20693354974⟩,
    ⟨277, 65187, 20735695728⟩,
    ⟨281, 65500, 20777276845⟩,
    ⟨283, 65655, 20818527800⟩,
    ⟨293, 66419, 20857890973⟩,
    ⟨307, 67460, 20894825495⟩,
    ⟨311, 67752, 20931159388⟩,
    ⟨313, 67897, 20967230540⟩,
    ⟨317, 68185, 21002725676⟩,
    ⟨331, 69174, 21036189554⟩,
    ⟨337, 69590, 21068873759⟩,
    ⟨347, 70272, 21100295013⟩,
    ⟨349, 70406, 21131510239⟩,
    ⟨353, 70674, 21162276738⟩,
    ⟨359, 71072, 21192369380⟩,
    ⟨367, 71596, 21221589452⟩,
    ⟨373, 71985, 21250194126⟩,
    ⟨379, 72368, 21278204499⟩,
    ⟨383, 72622, 21305843264⟩,
    ⟨389, 72999, 21332922856⟩,
    ⟨397, 73496, 21359276343⟩,
    ⟨401, 73742, 21385295374⟩,
    ⟨409, 74230, 21410637666⟩,
    ⟨419, 74830, 21435168448⟩,
    ⟨421, 74949, 21459564705⟩,
    ⟨431, 75537, 21483201078⟩,
    ⟨433, 75654, 21506711325⟩,
    ⟨439, 76002, 21529799858⟩,
    ⟨443, 76232, 21552622539⟩,
    ⟨449, 76575, 21575044998⟩,
    ⟨457, 77027, 21596944831⟩,
    ⟨461, 77251, 21618602180⟩,
    ⟨463, 77362, 21640150561⟩,
    ⟨467, 77585, 21661463826⟩,
    ⟨479, 78243, 21682056720⟩,
    ⟨487, 78677, 21702199532⟩,
    ⟨491, 78891, 21722132341⟩,
    ⟨499, 79318, 21741639957⟩,
    ⟨503, 79529, 21760949146⟩,
    ⟨509, 79844, 21779959190⟩,
    ⟨521, 80467, 21798379071⟩,
    ⟨523, 80569, 21816716192⟩,
    ⟨541, 81483, 21834225217⟩,
    ⟨547, 81783, 21851481629⟩,
    ⟨557, 82279, 21868322521⟩,
    ⟨563, 82573, 21884927196⟩,
    ⟨569, 82865, 21901301436⟩,
    ⟨571, 82962, 21917608261⟩,
    ⟨577, 83252, 21933692156⟩,
    ⟨587, 83730, 21949408269⟩,
    ⟨593, 84014, 21964915032⟩,
    ⟨599, 84297, 21980217594⟩,
    ⟨601, 84391, 21995460223⟩,
    ⟨607, 84671, 22010504593⟩,
    ⟨613, 84949, 22025355131⟩,
    ⟨617, 85133, 22040082059⟩,
    ⟨619, 85225, 22054752847⟩,
    ⟨631, 85772, 22069047467⟩,
    ⟨641, 86223, 22083042884⟩,
    ⟨643, 86312, 22096986634⟩,
    ⟨647, 86491, 22110819838⟩,
    ⟨653, 86757, 22124485521⟩,
    ⟨659, 87022, 22137987388⟩,
    ⟨661, 87110, 22151440880⟩,
    ⟨673, 87634, 22164571026⟩,
    ⟨677, 87808, 22177601710⟩,
    ⟨683, 88066, 22190481445⟩,
    ⟨691, 88409, 22203162550⟩,
    ⟨701, 88833, 22215600760⟩,
    ⟨709, 89170, 22227851974⟩,
    ⟨719, 89587, 22239874441⟩,
    ⟨727, 89918, 22251720533⟩,
    ⟨733, 90165, 22263438923⟩,
    ⟨739, 90410, 22275031850⟩,
    ⟨743, 90573, 22286544522⟩,
    ⟨751, 90897, 22297893714⟩,
    ⟨757, 91138, 22309124248⟩,
    ⟨761, 91299, 22320278980⟩,
    ⟨769, 91617, 22331278814⟩,
    ⟨773, 91776, 22342205467⟩,
    ⟨787, 92327, 22352869479⟩,
    ⟨797, 92716, 22363353835⟩,
    ⟨809, 93179, 22373628614⟩,
    ⟨811, 93256, 22383873144⟩,
    ⟨821, 93638, 22393950265⟩,
    ⟨823, 93714, 22403998082⟩,
    ⟨827, 93865, 22413983159⟩,
    ⟨829, 93941, 22423939473⟩,
    ⟨839, 94317, 22433736486⟩,
    ⟨853, 94839, 22443316279⟩,
    ⟨857, 94987, 22452838421⟩,
    ⟨859, 95060, 22462333824⟩,
    ⟨863, 95208, 22471772603⟩,
    ⟨877, 95720, 22481007781⟩,
    ⟨881, 95865, 22490188823⟩,
    ⟨883, 95938, 22499344990⟩,
    ⟨887, 96082, 22508447781⟩,
    ⟨907, 96799, 22517278230⟩,
    ⟨911, 96941, 22526058632⟩,
    ⟨919, 97224, 22534737103⟩,
    ⟨929, 97576, 22543290311⟩,
    ⟨937, 97855, 22551746073⟩,
    ⟨941, 97994, 22560155424⟩,
    ⟨947, 98202, 22568494487⟩,
    ⟨953, 98409, 22576764265⟩,
    ⟨967, 98888, 22584872225⟩,
    ⟨971, 99024, 22592937022⟩,
    ⟨977, 99228, 22600936513⟩,
    ⟨983, 99431, 22608871596⟩,
    ⟨991, 99700, 22616721234⟩,
    ⟨997, 99900, 22624508394⟩
  ]

private def listed : List ℕ := rows.map CubicProductRow.prime
private def smallDivisors : List ℕ := [2,3,5,7,11,13,17,19,23,29,31]

private theorem checked_product : productCheck roundScale rows=true := by
  decide +kernel

private theorem listed_nodup : listed.Nodup := by
  decide +kernel

private theorem checked_coverage :
    ∀ n : Fin 1001, 2≤n.val → n.val∈listed ∨
      (smallDivisors.any (fun d=>decide (2≤d ∧ d<n.val ∧ n.val%d=0)))=true := by
  decide +kernel

private theorem prime_mem_listed (p : ℕ) (hp : p.Prime) (hbound : p≤1000) :
    p∈listed := by
  have hc:=checked_coverage ⟨p,by omega⟩ hp.two_le
  rcases hc with hc|hc
  · exact hc
  · obtain ⟨d,_,hd⟩:=List.any_eq_true.mp hc
    have hdiv : 2≤d ∧ d<p ∧ p%d=0 := of_decide_eq_true hd
    rcases hp.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hdiv.2.2) with he|he
    · omega
    · omega

private theorem listed_product_le : (listed.map cubicWeightedFactor).prod≤227 := by
  have h:=productCheck_sound rows roundScale checked_product
  simpa only [listed,List.map_map,Function.comp_def,div_self
    (show (roundScale : ℝ)≠0 by norm_num [roundScale]),one_mul] using h

theorem cubic_factor_product_le :
    (∏ p∈(Finset.range 1001).filter Nat.Prime,cubicWeightedFactor p)≤227 := by
  have hsubset : (Finset.range 1001).filter Nat.Prime⊆listed.toFinset := by
    intro p hp
    obtain ⟨hrange,hprime⟩:=Finset.mem_filter.mp hp
    exact List.mem_toFinset.mpr
      (prime_mem_listed p hprime (by have := Finset.mem_range.mp hrange; omega))
  have hprod:=Finset.prod_le_prod_of_subset_of_one_le (f:=cubicWeightedFactor) hsubset
    (fun p _=>factor_nonneg p) (fun p _ _=>factor_one_le p)
  rw [List.prod_toFinset cubicWeightedFactor listed_nodup] at hprod
  exact hprod.trans listed_product_le

/-- The real-valued factor agrees with the literal absolute cubic Euler factor
on every prime, including its exceptional p=2 value. -/
theorem cubicWeightedFactor_eq (p : ℕ) (hp : p.Prime) :
    cubicWeightedFactor p =
      if p=2 then 3/2+(3/4 : ℝ)*(2 : ℝ)^(2/3 : ℝ)
      else 1+4*(p : ℝ)^(1/3 : ℝ)/((p : ℝ)*((p : ℝ)-2))+
        (3*(p : ℝ)+2)*(p : ℝ)^(2/3 : ℝ)/((p : ℝ)^2*((p : ℝ)-2))+
        2/((p : ℝ)*((p : ℝ)-2)) := by
  by_cases hp2 : p=2
  · subst p
    simp [cubicWeightedFactor]
  · have hp3 : 3≤p := by have := hp.two_le; omega
    have hpR : (3 : ℝ)≤p := by exact_mod_cast hp3
    have hp0 : (p : ℝ)≠0 := by linarith
    have hpm : (p : ℝ)-2≠0 := by linarith
    simp only [cubicWeightedFactor,hp2,if_false,denominator,Nat.cast_mul,Nat.cast_pow,
      Nat.cast_sub (by omega : 2≤p),Nat.cast_ofNat]
    field_simp [hp0,hpm] <;> ring

/-- Finite quantitative bound for the actual one-third absolute Euler factors. -/
theorem finite_cubic_weight_product_le :
    (∏ p∈(Finset.range 1001).filter Nat.Prime,
      if p=2 then 3/2+(3/4 : ℝ)*(2 : ℝ)^(2/3 : ℝ)
      else 1+4*(p : ℝ)^(1/3 : ℝ)/((p : ℝ)*((p : ℝ)-2))+
        (3*(p : ℝ)+2)*(p : ℝ)^(2/3 : ℝ)/((p : ℝ)^2*((p : ℝ)-2))+
        2/((p : ℝ)*((p : ℝ)-2)))≤227 := by
  calc
    _ = ∏ p∈(Finset.range 1001).filter Nat.Prime,cubicWeightedFactor p := by
      apply Finset.prod_congr rfl
      intro p hp
      exact (cubicWeightedFactor_eq p (Finset.mem_filter.mp hp).2).symm
    _ ≤ 227 := cubic_factor_product_le

end PrimePairFiniteConstants





set_option autoImplicit false
open scoped BigOperators

namespace RamareAnalytic

/-!
Quantitative Chebyshev power tails for the weighted Euler
product. The prime-power logarithmic tail is derived from the actual theta
bound and the integral test, without assuming convergence or a prime-tail
estimate. Intended pin: Lean 4.33.1 / Mathlib 0df444a.

Use m=1001, s=8/5 and s=6/5. These are the two power tails required by the
alpha=2/5 Euler factor. The finite factor certificate, division by log(1000),
and final product assembly are deliberately separate from this component.
-/

/-- Decreasing nonnegative weights preserve an inequality of all prefix sums. -/
theorem sum_weighted_le_of_prefix_le
    (a b w : ℕ → ℝ) (hw : ∀ n, 0 ≤ w n) (hanti : Antitone w)
    (hab : ∀ N, (∑ i ∈ Finset.range N, a i) ≤ ∑ i ∈ Finset.range N, b i)
    (N : ℕ) :
    (∑ i ∈ Finset.range N, w i * a i) ≤ ∑ i ∈ Finset.range N, w i * b i := by
  have hparts (c : ℕ → ℝ) :
      (∑ i ∈ Finset.range N, w i * c i) =
      w (N - 1) * (∑ i ∈ Finset.range N, c i) +
        ∑ i ∈ Finset.range (N - 1),
          (w i - w (i + 1)) * (∑ j ∈ Finset.range (i + 1), c j) := by
    have h := Finset.sum_range_by_parts w c N
    simp only [smul_eq_mul] at h
    rw [h, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hparts a, hparts b]
  apply add_le_add (mul_le_mul_of_nonneg_left (hab N) (hw (N - 1)))
  apply Finset.sum_le_sum
  intro i hi
  exact mul_le_mul_of_nonneg_left (hab (i + 1))
    (sub_nonneg.mpr (hanti (Nat.le_succ i)))

/-- Linear control on shifted prefix sums gives the sharp elementary power-tail constant. -/
theorem shifted_rpow_tail_of_prefix_le
    (a : ℕ → ℝ) (A : ℝ) (m : ℕ) (s : ℝ)
    (hA : 0 ≤ A) (hm : 1 ≤ m) (hs : 1 < s)
    (ha : ∀ n, 0 ≤ a n)
    (hprefix : ∀ N, (∑ i ∈ Finset.range (N + 1), a i) ≤ A * ((m : ℝ) + (N : ℝ))) :
    Summable (fun i : ℕ => a i * ((m + i : ℕ) : ℝ) ^ (-s)) ∧
      (∑' i : ℕ, a i * ((m + i : ℕ) : ℝ) ^ (-s)) ≤
        A * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by
  let w : ℕ → ℝ := fun i => ((m + i : ℕ) : ℝ) ^ (-s)
  let b : ℕ → ℝ := fun i => if i = 0 then A * (m : ℝ) else A
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hmR
  have hspos : 0 < s := zero_lt_one.trans hs
  have hsmpos : 0 < s - 1 := sub_pos.mpr hs
  have hsm0 : s - 1 ≠ 0 := hsmpos.ne'
  have hb (N : ℕ) :
      (∑ i ∈ Finset.range (N + 1), b i) = A * ((m : ℝ) + (N : ℝ)) := by
    simp [b, Finset.sum_range_succ']
    <;> ring
  have hab : ∀ N, (∑ i ∈ Finset.range N, a i) ≤ ∑ i ∈ Finset.range N, b i := by
    intro N
    cases N with
    | zero => simp
    | succ N => rw [hb]; exact hprefix N
  have hw : ∀ n, 0 ≤ w n := fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hanti : Antitone w := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos
    · have hmi : 0 < m + i := by omega
      exact_mod_cast hmi
    · exact_mod_cast Nat.add_le_add_left hij m
    · linarith
  have hantiR : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Ici (m : ℝ)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hmpos.trans_le hx) hxy (by linarith)
  have hint := integrableOn_Ioi_rpow_of_lt (show -s < -1 by linarith) hmpos
  have htail (N : ℕ) :
      (∑ i ∈ Finset.range N, w (i + 1)) ≤ (m : ℝ) ^ (1 - s) / (s - 1) := by
    have heq : (∑ i ∈ Finset.Ico m (m + N), (((i + 1 : ℕ) : ℝ) ^ (-s))) =
        ∑ i ∈ Finset.range N, w (i + 1) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left, w, Nat.add_assoc]
    rw [← heq]
    calc
      _ ≤ ∫ x : ℝ in Set.Ioi (m : ℝ), x ^ (-s) := by
        apply (hantiR.mono Set.Icc_subset_Ici_self).sum_Ico_le_integral hint
        intro x hx
        exact Real.rpow_nonneg (hmpos.trans hx).le _
      _ = (m : ℝ) ^ (1 - s) / (s - 1) := by
        rw [integral_Ioi_rpow_of_lt (show -s < -1 by linarith) hmpos,
          show -s + 1 = 1 - s by ring]
        have hn : 1 - s ≠ 0 := by linarith
        field_simp
        <;> ring
  have hpower : (m : ℝ) * (m : ℝ) ^ (-s) = (m : ℝ) ^ (1 - s) := by
    rw [show 1 - s = 1 + (-s) by ring, Real.rpow_add hmpos, Real.rpow_one]
  have hweighted_b (N : ℕ) :
      (∑ i ∈ Finset.range (N + 1), w i * b i) =
        A * ((m : ℝ) * w 0 + ∑ i ∈ Finset.range N, w (i + 1)) := by
    simp [b, Finset.sum_range_succ']
    rw [← Finset.sum_mul]
    ring
  have hfinite (N : ℕ) :
      (∑ i ∈ Finset.range (N + 1), w i * a i) ≤
        A * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (N + 1), w i * b i :=
        sum_weighted_le_of_prefix_le a b w hw hanti hab (N + 1)
      _ = A * ((m : ℝ) * w 0 + ∑ i ∈ Finset.range N, w (i + 1)) := hweighted_b N
      _ ≤ A * ((m : ℝ) * w 0 + (m : ℝ) ^ (1 - s) / (s - 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (htail N)) hA
      _ = _ := by
        simp only [w, Nat.add_zero, hpower]
        field_simp
        <;> ring
  have hnonneg : ∀ i, 0 ≤ w i * a i := fun i => mul_nonneg (hw i) (ha i)
  have hrange : ∀ N, (∑ i ∈ Finset.range N, w i * a i) ≤
      A * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by
    intro N
    cases N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
    | succ N => exact hfinite N
  have hsum := summable_of_sum_range_le hnonneg hrange
  have hbound := Real.tsum_le_of_sum_range_le hnonneg hrange
  simpa only [w, mul_comm] using And.intro hsum hbound

/-- Chebyshev's theta estimate bounds prime logarithms weighted by p^(-s).
The index m+k enumerates every integer at least m exactly once. -/
theorem prime_power_log_tail (m : ℕ) (hm : 1 ≤ m) (s : ℝ) (hs : 1 < s) :
    Summable (fun k : ℕ =>
      if (m + k).Prime then Real.log ((m + k : ℕ) : ℝ) * ((m + k : ℕ) : ℝ) ^ (-s)
      else 0) ∧
    (∑' k : ℕ, if (m + k).Prime then
      Real.log ((m + k : ℕ) : ℝ) * ((m + k : ℕ) : ℝ) ^ (-s) else 0) ≤
      Real.log 4 * (s / (s - 1)) * (m : ℝ) ^ (1 - s) := by
  let c : ℕ → ℝ := fun p => if p.Prime then Real.log (p : ℝ) else 0
  have hc : ∀ n, 0 ≤ c n := by
    intro n
    dsimp only [c]
    split_ifs with hp
    · exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    · exact le_rfl
  have hprefix (N : ℕ) :
      (∑ i ∈ Finset.range (N + 1), c (m + i)) ≤ Real.log 4 * ((m : ℝ) + (N : ℝ)) := by
    calc
      _ = ∑ i ∈ Finset.Ico m (m + N + 1), c i := by
        rw [Finset.sum_Ico_eq_sum_range,
          show m + N + 1 - m = N + 1 by omega]
      _ ≤ ∑ i ∈ Finset.range (m + N + 1), c i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          exact Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
        · intro i hi hi'
          exact hc i
      _ = Chebyshev.theta ((m + N : ℕ) : ℝ) := by
        rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast,
          ← Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
      _ ≤ Real.log 4 * ((m + N : ℕ) : ℝ) :=
        Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg _)
      _ = _ := by rw [Nat.cast_add]
  have h := shifted_rpow_tail_of_prefix_le (fun i => c (m + i))
    (Real.log 4) m s (Real.log_nonneg (by norm_num)) hm hs
    (fun i => hc (m + i)) hprefix
  simpa only [c, ite_mul, zero_mul] using h

end RamareAnalytic



set_option autoImplicit false
set_option maxRecDepth 8192
open scoped BigOperators

namespace RamareWeightedConstants

/-!
Three finite analytic certificates used by WeightedEulerAssembly.lean.
The two generic logarithm lemmas below copy the checked GammaCertificate.lean
proofs, under a separate namespace. Ground inequalities use exact rationals;
the fifth-root certificate uses a monotone fifth power on nonnegative reals.
This file is a local component, not a separate platform publication.
-/

/-- A rational lower bound from the nonnegative odd-power logarithm series. -/
private def logLower (x : ℚ) (terms : ℕ) : ℚ :=
  2 * ∑ i ∈ Finset.range terms,
    ((x - 1) / (x + 1)) ^ (2 * i + 1) / (2 * i + 1 : ℕ)

private theorem logLower_le (x : ℚ) (hx : 1 ≤ x) (terms : ℕ) :
    (logLower x terms : ℝ) ≤ Real.log (x : ℝ) := by
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hden : (0 : ℝ) < (x : ℝ) + 1 := by linarith
  have hnonneg : (0 : ℝ) ≤ ((x : ℝ) - 1) / ((x : ℝ) + 1) :=
    div_nonneg (by linarith) hden.le
  have hlt : ((x : ℝ) - 1) / ((x : ℝ) + 1) < 1 := by
    apply (div_lt_one hden).2
    linarith
  have hratio :
      (1 + ((x : ℝ) - 1) / ((x : ℝ) + 1)) /
        (1 - ((x : ℝ) - 1) / ((x : ℝ) + 1)) = (x : ℝ) := by
    field_simp
    ring
  have h := Real.sum_range_le_log_div hnonneg hlt terms
  rw [hratio] at h
  unfold logLower
  push_cast
  linarith

/-- Range reduction keeps the logarithm-series argument at most one third
when `2^k ≤ N ≤ 2^(k+1)`. Only the lower inequality is needed for soundness. -/
private def logLowerNat (N k terms : ℕ) : ℚ :=
  (k : ℚ) * logLower 2 terms + logLower ((N : ℚ) / 2 ^ k) terms

private theorem logLowerNat_le (N k terms : ℕ) (hN : 2 ^ k ≤ N) :
    (logLowerNat N k terms : ℝ) ≤ Real.log (N : ℝ) := by
  have hpow : (0 : ℚ) < 2 ^ k := by positivity
  have hpowR : (0 : ℝ) < 2 ^ k := by positivity
  have hNpos : 0 < N := lt_of_lt_of_le (by positivity) hN
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hratio : (1 : ℚ) ≤ (N : ℚ) / 2 ^ k := by
    apply (le_div_iff₀ hpow).2
    simpa using (show (2 : ℚ) ^ k ≤ N by exact_mod_cast hN)
  have htwo := logLower_le 2 (by norm_num) terms
  norm_num at htwo
  have hrest := logLower_le ((N : ℚ) / 2 ^ k) hratio terms
  have hmult := mul_le_mul_of_nonneg_left htwo (show (0 : ℝ) ≤ k by positivity)
  have hid : (2 : ℝ) ^ k * ((N : ℝ) / 2 ^ k) = N := by
    field_simp
  have hlog := Real.log_mul hpowR.ne' (div_pos hNposR hpowR).ne'
  rw [hid, Real.log_pow] at hlog
  unfold logLowerNat
  push_cast at hrest ⊢
  linarith

private theorem log_thousand_rational_certificate :
    (69 : ℚ) / 10 ≤ logLowerNat 1000 9 9 := by
  decide +kernel

theorem log_thousand_lower : (69 / 10 : ℝ) ≤ Real.log 1000 := by
  have hrat : (69 / 10 : ℝ) ≤ (logLowerNat 1000 9 9 : ℝ) := by
    have hcR := (Rat.cast_le (K := ℝ)).2 log_thousand_rational_certificate
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hcR
  exact hrat.trans (by
    simpa only [Nat.cast_ofNat] using logLowerNat_le 1000 9 9 (by decide +kernel))

private theorem log_seven_fifths_rational_certificate :
    (1 : ℚ) / 3 ≤ logLower (7 / 5) 2 := by
  decide +kernel

theorem log_seven_fifths_lower : (1 / 3 : ℝ) ≤ Real.log (7 / 5 : ℝ) := by
  have hrat : (1 / 3 : ℝ) ≤ (logLower (7 / 5) 2 : ℝ) := by
    have hcR := (Rat.cast_le (K := ℝ)).2 log_seven_fifths_rational_certificate
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hcR
  exact hrat.trans (by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      logLower_le (7 / 5) (by norm_num) 2)

theorem thousand_negative_fifth_upper :
    (1000 : ℝ) ^ (-(1 / 5 : ℝ)) ≤ (63 / 250 : ℝ) := by
  have hp : 0 ≤ (1000 : ℝ) ^ (1 / 5 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have hpow : ((1000 : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) = 1000 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1000)]
    norm_num
  have hbase : (250 / 63 : ℝ) ≤ (1000 : ℝ) ^ (1 / 5 : ℝ) := by
    apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 250 / 63) hp
      (by norm_num : (5 : ℕ) ≠ 0)).mp
    rw [hpow]
    norm_num
  have hinv : ((1000 : ℝ) ^ (1 / 5 : ℝ))⁻¹ ≤ (63 / 250 : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1000) _)).mpr
    nlinarith [hbase]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1000)]
  exact hinv

end RamareWeightedConstants


/-!
Append to the exact passed PrimePowerTail and WeightedEulerConstants parents.
This derives the cubic absolute Euler-factor tail from actual Chebyshev bounds;
no prime-tail estimate or numerical constant is assumed in the exported result.
-/

namespace PrimePairFiniteConstants

noncomputable def cubicWeightIncrement (p : ℕ) : ℝ :=
  4*(p : ℝ)^(1/3 : ℝ)/((p : ℝ)*((p : ℝ)-2))+
    (3*(p : ℝ)+2)*(p : ℝ)^(2/3 : ℝ)/((p : ℝ)^2*((p : ℝ)-2))+
    2/((p : ℝ)*((p : ℝ)-2))

noncomputable def cubicIncrementTail (p : ℕ) : ℝ :=
  if 1000≤p ∧ p.Prime then cubicWeightIncrement p else 0

private noncomputable def cubicPowerTail (s : ℝ) (p : ℕ) : ℝ :=
  if 1000≤p ∧ p.Prime then Real.log (p : ℝ)*(p : ℝ)^(-s) else 0

private theorem cubicIncrementTail_nonneg (p : ℕ) : 0≤cubicIncrementTail p := by
  unfold cubicIncrementTail
  split_ifs with hp
  · have hR : (1000 : ℝ)≤p := by exact_mod_cast hp.1
    have hp0 : 0<(p : ℝ) := by linarith
    have hp2 : 0<(p : ℝ)-2 := by linarith
    dsimp [cubicWeightIncrement]
    positivity
  · exact le_rfl

private theorem power_tail_unshifted (s : ℝ) (hs : 1<s) :
    Summable (cubicPowerTail s) ∧
      (∑' p : ℕ,cubicPowerTail s p)≤
        Real.log 4*(s/(s-1))*(1000 : ℝ)^(1-s) := by
  have h:=RamareAnalytic.prime_power_log_tail 1000 (by norm_num) s hs
  have heq : (fun k : ℕ=>cubicPowerTail s (k+1000))=
      (fun k : ℕ=>if (1000+k).Prime then
        Real.log ((1000+k : ℕ) : ℝ)*((1000+k : ℕ) : ℝ)^(-s) else 0) := by
    funext k
    rw [Nat.add_comm k 1000]
    have hk : 1000≤1000+k := by omega
    simp only [cubicPowerTail,hk,true_and]
  have hshift : Summable (fun k : ℕ=>cubicPowerTail s (k+1000)) := by
    rw [heq]
    exact h.1
  have hglobal:=(summable_nat_add_iff 1000).mp hshift
  have hzero : (∑ p∈Finset.range 1000,cubicPowerTail s p)=0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hn : ¬1000≤p := by have := Finset.mem_range.mp hp; omega
    simp [cubicPowerTail,hn]
  have hsum:=hglobal.sum_add_tsum_nat_add 1000
  rw [hzero,zero_add,heq] at hsum
  exact ⟨hglobal,hsum ▸ h.2⟩

private theorem increment_le_log_power_majorant (p : ℕ) (hp : 1000≤p) :
    cubicWeightIncrement p≤((500/499 : ℝ)*(10/69 : ℝ))*
      (4*(Real.log (p : ℝ)*(p : ℝ)^(-(5/3 : ℝ)))+
        (1501/500 : ℝ)*(Real.log (p : ℝ)*(p : ℝ)^(-(4/3 : ℝ)))+
        2*(Real.log (p : ℝ)*(p : ℝ)^(-(2 : ℝ)))) := by
  have hpR : (1000 : ℝ)≤p := by exact_mod_cast hp
  have hp0 : 0<(p : ℝ) := by linarith
  have hp2 : 0<(p : ℝ)-2 := by linarith
  have hrecip : 1/((p : ℝ)*((p : ℝ)-2))≤(500/499 : ℝ)/(p : ℝ)^2 := by
    apply (div_le_div_iff₀ (mul_pos hp0 hp2) (sq_pos_of_pos hp0)).mpr
    have hpoly:=mul_nonneg hp0.le (show 0≤(p : ℝ)-1000 by linarith)
    nlinarith
  have hcoef : 3+2/(p : ℝ)≤(1501/500 : ℝ) := by
    have hdiv : 2/(p : ℝ)≤(1/500 : ℝ) := (div_le_iff₀ hp0).mpr (by linarith)
    linarith
  have hid : cubicWeightIncrement p=
      (4*(p : ℝ)^(1/3 : ℝ)+(3+2/(p : ℝ))*(p : ℝ)^(2/3 : ℝ)+2)*
        (1/((p : ℝ)*((p : ℝ)-2))) := by
    dsimp [cubicWeightIncrement]
    field_simp [hp0.ne',hp2.ne'] <;> ring
  have hn : 4*(p : ℝ)^(1/3 : ℝ)+(3+2/(p : ℝ))*(p : ℝ)^(2/3 : ℝ)+2≤
      4*(p : ℝ)^(1/3 : ℝ)+(1501/500 : ℝ)*(p : ℝ)^(2/3 : ℝ)+2 := by
    have h:=mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hp0.le (2/3 : ℝ))
    linarith
  have hpow1 : (p : ℝ)^(-(5/3 : ℝ))=(p : ℝ)^(1/3 : ℝ)/(p : ℝ)^2 := by
    rw [show -(5/3 : ℝ)=(1/3 : ℝ)-2 by norm_num,Real.rpow_sub hp0,Real.rpow_two]
  have hpow2 : (p : ℝ)^(-(4/3 : ℝ))=(p : ℝ)^(2/3 : ℝ)/(p : ℝ)^2 := by
    rw [show -(4/3 : ℝ)=(2/3 : ℝ)-2 by norm_num,Real.rpow_sub hp0,Real.rpow_two]
  have hpow3 : (p : ℝ)^(-(2 : ℝ))=1/(p : ℝ)^2 := by
    rw [Real.rpow_neg hp0.le,Real.rpow_two,one_div]
  have hpow : cubicWeightIncrement p≤(500/499 : ℝ)*
      (4*(p : ℝ)^(-(5/3 : ℝ))+(1501/500 : ℝ)*(p : ℝ)^(-(4/3 : ℝ))+
        2*(p : ℝ)^(-(2 : ℝ))) := by
    calc
      _ = _ := hid
      _ ≤ (4*(p : ℝ)^(1/3 : ℝ)+(1501/500 : ℝ)*(p : ℝ)^(2/3 : ℝ)+2)*
          ((500/499 : ℝ)/(p : ℝ)^2) := mul_le_mul hn hrecip (by positivity) (by positivity)
      _ = _ := by rw [hpow1,hpow2,hpow3]; ring
  have hlog : (69/10 : ℝ)≤Real.log (p : ℝ) :=
    RamareWeightedConstants.log_thousand_lower.trans (Real.log_le_log (by norm_num) hpR)
  have hone : (1 : ℝ)≤(10/69 : ℝ)*Real.log (p : ℝ) := by linarith
  have hpos : 0≤4*(p : ℝ)^(-(5/3 : ℝ))+(1501/500 : ℝ)*(p : ℝ)^(-(4/3 : ℝ))+
      2*(p : ℝ)^(-(2 : ℝ)) := by positivity
  calc
    _ ≤ _ := hpow
    _ ≤ (500/499 : ℝ)*(((10/69 : ℝ)*Real.log (p : ℝ))*
        (4*(p : ℝ)^(-(5/3 : ℝ))+(1501/500 : ℝ)*(p : ℝ)^(-(4/3 : ℝ))+
          2*(p : ℝ)^(-(2 : ℝ)))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hone hpos
    _ = _ := by ring

private theorem thousand_negative_cube_root : (1000 : ℝ)^(-(1/3 : ℝ))=1/10 := by
  have hc : (1000 : ℝ)^(1/3 : ℝ)=10 := by
    simpa only [Nat.cast_ofNat, one_div,
      show (10 : ℝ)^3=(1000 : ℝ) by norm_num] using
      (Real.pow_rpow_inv_natCast (by norm_num : (0 : ℝ)≤10)
        (by decide : (3 : ℕ)≠0))
  rw [Real.rpow_neg (by norm_num : (0 : ℝ)≤1000),hc]
  norm_num

private theorem thousand_negative_two_thirds : (1000 : ℝ)^(-(2/3 : ℝ))=1/100 := by
  calc
    _ = ((1000 : ℝ)^(-(1/3 : ℝ)))^2 := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ)≤1000)]
      norm_num
    _ = _ := by rw [thousand_negative_cube_root]; norm_num

/-- Actual cubic local increments have a summable tail with a rational bound. -/
theorem cubic_increment_tail_le :
    Summable cubicIncrementTail ∧ (∑' p : ℕ,cubicIncrementTail p)≤(27/100 : ℝ) := by
  have h5:=power_tail_unshifted (5/3 : ℝ) (by norm_num)
  have h4:=power_tail_unshifted (4/3 : ℝ) (by norm_num)
  have h2:=power_tail_unshifted 2 (by norm_num)
  have hlog4 : Real.log 4≤(7/5 : ℝ) := by
    rw [Real.log_four_eq]
    have h:=Real.log_two_lt_d9
    linarith
  have hb5 : (∑' p : ℕ,cubicPowerTail (5/3 : ℝ) p)≤(7/5 : ℝ)*(5/2 : ℝ)*(1/100 : ℝ) := by
    have h : (∑' p : ℕ,cubicPowerTail (5/3 : ℝ) p)≤Real.log 4*(5/2 : ℝ)*(1/100 : ℝ) := by
      simpa only [show (5/3 : ℝ)/(5/3-1)=5/2 by norm_num,
        show (1 : ℝ)-5/3=-(2/3 : ℝ) by norm_num,thousand_negative_two_thirds] using h5.2
    nlinarith
  have hb4 : (∑' p : ℕ,cubicPowerTail (4/3 : ℝ) p)≤(7/5 : ℝ)*4*(1/10 : ℝ) := by
    have h : (∑' p : ℕ,cubicPowerTail (4/3 : ℝ) p)≤Real.log 4*4*(1/10 : ℝ) := by
      simpa only [show (4/3 : ℝ)/(4/3-1)=4 by norm_num,
        show (1 : ℝ)-4/3=-(1/3 : ℝ) by norm_num,thousand_negative_cube_root] using h4.2
    nlinarith
  have hb2 : (∑' p : ℕ,cubicPowerTail 2 p)≤(7/5 : ℝ)*2*(1/1000 : ℝ) := by
    have h : (∑' p : ℕ,cubicPowerTail 2 p)≤Real.log 4*2*(1/1000 : ℝ) := by
      norm_num at h2 ⊢
      exact h2.2
    nlinarith
  let K : ℝ:=(500/499 : ℝ)*(10/69 : ℝ)
  have hK : 0≤K := by norm_num [K]
  have hmajor : ∀ p : ℕ,cubicIncrementTail p≤K*
      (4*cubicPowerTail (5/3 : ℝ) p+(1501/500 : ℝ)*cubicPowerTail (4/3 : ℝ) p+
        2*cubicPowerTail 2 p) := by
    intro p
    by_cases hp : 1000≤p ∧ p.Prime
    · simpa only [cubicIncrementTail,cubicPowerTail,if_pos hp,K] using
        increment_le_log_power_majorant p hp.1
    · simp only [cubicIncrementTail,cubicPowerTail,if_neg hp,mul_zero,add_zero,le_refl]
  have hG:=((h5.1.mul_left 4).add (h4.1.mul_left (1501/500 : ℝ))).add (h2.1.mul_left 2)
  have hGK:=hG.mul_left K
  have hV:=Summable.of_nonneg_of_le cubicIncrementTail_nonneg hmajor hGK
  have hsum:=(((h5.1.hasSum.mul_left 4).add
    (h4.1.hasSum.mul_left (1501/500 : ℝ))).add (h2.1.hasSum.mul_left 2)).mul_left K
  refine ⟨hV,?_⟩
  calc
    _ ≤ ∑' p : ℕ,K*(4*cubicPowerTail (5/3 : ℝ) p+
        (1501/500 : ℝ)*cubicPowerTail (4/3 : ℝ) p+2*cubicPowerTail 2 p) :=
      Summable.tsum_le_tsum hmajor hV hGK
    _ = K*(4*(∑' p : ℕ,cubicPowerTail (5/3 : ℝ) p)+
        (1501/500 : ℝ)*(∑' p : ℕ,cubicPowerTail (4/3 : ℝ) p)+
        2*(∑' p : ℕ,cubicPowerTail 2 p)) := hsum.tsum_eq
    _ ≤ K*(4*((7/5 : ℝ)*(5/2 : ℝ)*(1/100 : ℝ))+
        (1501/500 : ℝ)*((7/5 : ℝ)*4*(1/10 : ℝ))+2*((7/5 : ℝ)*2*(1/1000 : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ hK
      nlinarith
    _ ≤ (27/100 : ℝ) := by norm_num [K]

private theorem log_tail_factor_lower : (27/100 : ℝ)≤Real.log (33/25 : ℝ) := by
  have h:=Real.sum_range_le_log_div (by norm_num : (0 : ℝ)≤4/29)
    (by norm_num : (4/29 : ℝ)<1) 1
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Uniform bound on each finite product of high-prime absolute factors. -/
theorem cubic_tail_product_le (S : Finset ℕ)
    (hS : ∀ p∈S,1000≤p ∧ p.Prime) :
    (∏ p∈S,(1+cubicWeightIncrement p))≤(33/25 : ℝ) := by
  have ht:=cubic_increment_tail_le
  have hsum : (∑ p∈S,cubicIncrementTail p)≤(27/100 : ℝ) :=
    (ht.1.sum_le_tsum S (fun p _=>cubicIncrementTail_nonneg p)).trans ht.2
  have hexp : Real.exp (27/100 : ℝ)≤(33/25 : ℝ) :=
    (Real.le_log_iff_exp_le (by norm_num)).mp log_tail_factor_lower
  calc
    _ = ∏ p∈S,(1+cubicIncrementTail p) := by
      apply Finset.prod_congr rfl
      intro p hp
      simp only [cubicIncrementTail,if_pos (hS p hp)]
    _ ≤ Real.exp (∑ p∈S,cubicIncrementTail p) :=
      Real.prod_one_add_le_exp_sum S cubicIncrementTail_nonneg
    _ ≤ (33/25 : ℝ) := (Real.exp_le_exp.mpr hsum).trans hexp

end PrimePairFiniteConstants



/-!
The actual cubic one-third moment is bounded by combining the exact finite
prime product, the high-prime product estimate, and the actual Euler limit.
-/

open scoped BigOperators Topology
open Filter

namespace PrimePairConvolution

private theorem cubic_weighted_finite_products_bound (N : ℕ) :
    (∏ p ∈ Nat.primesBelow N, cubicWeightedEulerFactor p) ≤ (7491 / 25 : ℝ) := by
  classical
  let S := Nat.primesBelow N
  let L := S.filter (fun p => p < 1000)
  let H := S.filter (fun p => ¬p < 1000)
  have hprime (p : ℕ) (hp : p ∈ S) : p.Prime := (Nat.mem_primesBelow.mp hp).2
  have hfinite :
      (∏ p ∈ (Finset.range 1001).filter Nat.Prime, cubicWeightedEulerFactor p) ≤ 227 := by
    simpa only [cubicWeightedEulerFactor] using
      PrimePairFiniteConstants.finite_cubic_weight_product_le
  have hlow : (∏ p ∈ L, cubicWeightedEulerFactor p) ≤ 227 := by
    have hsub : L ⊆ (Finset.range 1001).filter Nat.Prime := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpS, hcut⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hprime p hpS⟩
    have hprod := Finset.prod_le_prod_of_subset_of_one_le
      (f := cubicWeightedEulerFactor) hsub
      (fun p hp => (show (0 : ℝ) ≤ 1 by norm_num).trans
        (cubicWeightedEulerFactor_one_le p (hprime p (Finset.mem_filter.mp hp).1)))
      (fun p hp _ => cubicWeightedEulerFactor_one_le p (Finset.mem_filter.mp hp).2)
    exact hprod.trans hfinite
  have hhigh : (∏ p ∈ H, cubicWeightedEulerFactor p) ≤ (33 / 25 : ℝ) := by
    have hH : ∀ p ∈ H, 1000 ≤ p ∧ p.Prime := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpS, hcut⟩
      exact ⟨by omega, hprime p hpS⟩
    calc
      _ = ∏ p ∈ H, (1 + PrimePairFiniteConstants.cubicWeightIncrement p) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hp1000 := (hH p hp).1
        have hp2 : p ≠ 2 := by omega
        simp only [cubicWeightedEulerFactor, if_neg hp2,
          PrimePairFiniteConstants.cubicWeightIncrement]
        ring
      _ ≤ (33 / 25 : ℝ) := PrimePairFiniteConstants.cubic_tail_product_le H hH
  calc
    _ = (∏ p ∈ L, cubicWeightedEulerFactor p) *
        (∏ p ∈ H, cubicWeightedEulerFactor p) :=
      (Finset.prod_filter_mul_prod_filter_not S (fun p => p < 1000)
        cubicWeightedEulerFactor).symm
    _ ≤ (227 : ℝ) * (33 / 25 : ℝ) :=
      mul_le_mul hlow hhigh
        (Finset.prod_nonneg (fun p hp => (show (0 : ℝ) ≤ 1 by norm_num).trans
          (cubicWeightedEulerFactor_one_le p (hprime p (Finset.mem_filter.mp hp).1))))
        (by norm_num)
    _ = (7491 / 25 : ℝ) := by norm_num

/-- Quantitative one-third absolute moment for the published cubic coefficient
family, with convergence and the numerical bound both derived. -/
theorem cubic_oneThird_moment_bound
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    Summable (fun n : ℕ => |h n| * (n : ℝ)^(1 / 3 : ℝ)) ∧
      (∑' n : ℕ, |h n| * (n : ℝ)^(1 / 3 : ℝ)) ≤ (7491 / 25 : ℝ) ∧
      (∑' n : ℕ, |h n| * (n : ℝ)^(1 / 3 : ℝ)) < 300 := by
  have hsum := weighted_oneThird_summable_of_cubic_prime_power_values h hmul hpv hpz
  have hbound := cubic_weighted_moment_le_of_product_bound h hmul hpv hpz
    (7491 / 25) cubic_weighted_finite_products_bound
  exact ⟨hsum, hbound, hbound.trans_lt (by norm_num)⟩

end PrimePairConvolution

theorem solution
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    Summable (fun n : ℕ => |h n| * (n : ℝ)^(1 / 3 : ℝ)) ∧
      (∑' n : ℕ, |h n| * (n : ℝ)^(1 / 3 : ℝ)) ≤ (7491 / 25 : ℝ) ∧
      (∑' n : ℕ, |h n| * (n : ℝ)^(1 / 3 : ℝ)) < 300 := by
  exact PrimePairConvolution.cubic_oneThird_moment_bound h hmul hpv hpz

#print axioms solution
