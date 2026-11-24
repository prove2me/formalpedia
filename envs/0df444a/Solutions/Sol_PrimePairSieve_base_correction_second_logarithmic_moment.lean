-- Prove2me | solution 1 for PrimePairSieve.base_correction_second_logarithmic_moment
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T07:55:51.761722+00:00
-- url     : https://prove2.me/submissions/4c165bb6-afc9-4653-a152-f64dfbbe89c9

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.Topology.Order.MonotoneConvergence
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
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factors
import Mathlib.Data.Nat.Squarefree
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Indicator
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Topology.Algebra.InfiniteSum.Real



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
# The twin prime constant and Tao's pair-sieve weight

Source: Terence Tao, *Every odd number greater than 1 is the sum of at most
five primes*, https://arxiv.org/abs/1201.6656, proof of Proposition 4.10.

The twin prime constant is the Euler product
`𝔖₂ = 2 ∏_{p>2} (1 - 1/(p-1)²)`, and the multiplicative weight `f` used in
the prime-pair sieve expansion is
`f(n) = 𝟙_{(n,2)=1} μ²(n) ∏_{p|n, p>2} 1/(p-2)`.

The infinite product is defined as twice the infimum of its partial products
`∏_{2<p≤Q} (1 - 1/(p-1)²)` over `Q`. Since each factor lies in `(0,1)`, the
partial products form a decreasing sequence whose limit is this infimum, so
the value coincides with the infinite product; the infimum formulation keeps
the facts needed in sieve estimates (every finite partial product dominates
the full product) elementary, with no convergence machinery.
-/

open scoped BigOperators



set_option autoImplicit false
namespace TaoFivePrimes

private noncomputable def fullPartial (Q : ℕ) : ℝ :=
  ∏ p ∈ Finset.range (Q + 1), if 2 < p then 1 - 1 / ((p : ℝ) - 1)^2 else 1

private theorem fullPartial_formula (n : ℕ) :
    fullPartial (n + 2) = ((n : ℝ) + 2) / (2 * ((n : ℝ) + 1)) := by
  induction n with
  | zero => norm_num [fullPartial, Finset.prod_range_succ]
  | succ n ih =>
    have hrec : fullPartial (n + 1 + 2) =
        fullPartial (n + 2) * (1 - 1 / (((n + 3 : ℕ) : ℝ) - 1)^2) := by
      unfold fullPartial
      rw [show n + 1 + 2 + 1 = (n + 2 + 1) + 1 by omega, Finset.prod_range_succ]
      simp [show 2 < n + 2 + 1 by omega]
    rw [hrec, ih]
    push_cast
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    convert_to
      (((n : ℝ) + 2) / (2 * ((n : ℝ) + 1))) *
          (1 - 1 / ((n : ℝ) + 2)^2) =
        ((n : ℝ) + 3) / (2 * ((n : ℝ) + 2)) using 1 <;> try ring
    field_simp
    <;> ring

private theorem factor_nonneg (p : ℕ) (hp : 2 < p) :
    0 ≤ (1 : ℝ) - 1 / ((p : ℝ) - 1)^2 := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hsq : 1 ≤ ((p : ℝ) - 1)^2 := by nlinarith
  exact sub_nonneg.mpr ((div_le_one (by linarith : (0 : ℝ) < ((p : ℝ) - 1)^2)).mpr hsq)

private theorem fullPartial_le (Q : ℕ) : fullPartial Q ≤ twinPrimePartial Q := by
  unfold fullPartial twinPrimePartial
  apply Finset.prod_le_prod
  · intro p hp
    split_ifs with h
    · exact factor_nonneg p h
    · norm_num
  · intro p hp
    by_cases h : 2 < p
    · by_cases hprime : Nat.Prime p
      · simp [h, hprime]
      · simp only [h, hprime, false_and, if_false, if_true]
        exact sub_le_self _ (by positivity)
    · simp [h]

/-- A telescoping comparison product gives a uniform positive lower bound. -/
theorem twinPrimePartial_bounds (Q : ℕ) :
    (1 / 2 : ℝ) ≤ twinPrimePartial Q ∧ twinPrimePartial Q ≤ 1 := by
  constructor
  · have hfull : (1 / 2 : ℝ) ≤ fullPartial Q := by
      rcases Q with _ | _ | n
      · norm_num [fullPartial]
      · norm_num [fullPartial, Finset.prod_range_succ]
      · change (1 / 2 : ℝ) ≤ fullPartial (n + 2)
        rw [fullPartial_formula]
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1))).mpr
        linarith
    exact hfull.trans (fullPartial_le Q)
  · unfold twinPrimePartial
    apply Finset.prod_le_one
    · intro p hp
      split_ifs with h
      · exact factor_nonneg p h.2
      · norm_num
    · intro p hp
      split_ifs
      · exact sub_le_self _ (by positivity)
      · exact le_rfl

/-- Bounds use the actual public infimum definition, with no assumed product convergence. -/
theorem twinPrimeConstant_bounds : 1 ≤ twinPrimeConstant ∧ twinPrimeConstant ≤ 3 / 2 := by
  have hn : (Set.range twinPrimePartial).Nonempty := Set.range_nonempty _
  have hb : BddBelow (Set.range twinPrimePartial) :=
    ⟨1 / 2, by rintro _ ⟨Q, rfl⟩; exact (twinPrimePartial_bounds Q).1⟩
  have hlo : (1 / 2 : ℝ) ≤ sInf (Set.range twinPrimePartial) := by
    apply le_csInf hn
    rintro _ ⟨Q, rfl⟩
    exact (twinPrimePartial_bounds Q).1
  have hhi : sInf (Set.range twinPrimePartial) ≤ twinPrimePartial 3 :=
    csInf_le hb (Set.mem_range_self _)
  have hthree : twinPrimePartial 3 = 3 / 4 := by
    norm_num [twinPrimePartial, Finset.prod_range_succ, Nat.prime_three]
  rw [hthree] at hhi
  unfold twinPrimeConstant
  constructor <;> linarith

end TaoFivePrimes


/-!
The actual cubic correction has mass 1 / TaoFivePrimes.twinPrimeConstant.
The constant is the public literal infimum of partial products; no infinite
product definition, convergence premise, or replacement constant is used.

This fragment follows BaseEulerSummability and the exact checked
TwinConstantBounds source in one module. Root owns compilation.
-/

open scoped Topology
open Filter

namespace TaoFivePrimes

private theorem twinPrimePartial_antitone : Antitone twinPrimePartial := by
  apply antitone_nat_of_succ_le
  intro Q
  have hrec : twinPrimePartial (Q + 1) = twinPrimePartial Q *
      (if (Q + 1).Prime ∧ 2 < Q + 1 then
        1 - 1 / (((Q + 1 : ℕ) : ℝ) - 1)^2 else 1) := by
    unfold twinPrimePartial
    rw [Finset.prod_range_succ]
  rw [hrec]
  have hnonneg : 0 ≤ twinPrimePartial Q := by
    have h := (twinPrimePartial_bounds Q).1
    linarith
  have hfactor : (if (Q + 1).Prime ∧ 2 < Q + 1 then
      (1 : ℝ) - 1 / (((Q + 1 : ℕ) : ℝ) - 1)^2 else 1) ≤ 1 := by
    split_ifs
    · exact sub_le_self _ (by positivity)
    · exact le_rfl
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor hnonneg

/-- The public decreasing partial products converge to their defining infimum. -/
theorem twinPrimePartial_tendsto_sInf :
    Tendsto twinPrimePartial atTop (𝓝 (sInf (Set.range twinPrimePartial))) := by
  have hb : BddBelow (Set.range twinPrimePartial) :=
    ⟨1 / 2, by rintro _ ⟨Q, rfl⟩; exact (twinPrimePartial_bounds Q).1⟩
  change Tendsto twinPrimePartial atTop (𝓝 (⨅ Q : ℕ, twinPrimePartial Q))
  exact tendsto_atTop_ciInf twinPrimePartial_antitone hb

end TaoFivePrimes

namespace PrimePairConvolution

private theorem cubic_signed_prime_factor_cancellation
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0)
    (p : ℕ) :
    (if p.Prime then (∑' k : ℕ, h (p ^ k)) else 1) *
      (if p.Prime ∧ 2 < p then 1 - 1 / ((p : ℝ) - 1)^2 else 1) =
      if p = 2 then (1 / 2 : ℝ) else 1 := by
  by_cases hp : p.Prime
  · rw [if_pos hp, cubic_prime_power_tsum (fun n => h n) p
      (fun k hk => hpz p k hp hk), hmul.1,
      (hpv p hp).1, (hpv p hp).2.1, (hpv p hp).2.2]
    by_cases hp2 : p = 2
    · subst p
      norm_num
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hgt : 2 < p := by omega
      have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      have h0 : (p : ℝ) ≠ 0 := by linarith
      have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
      simp only [if_neg hp2, hp, hgt, and_self, if_true]
      field_simp [h0, h1, h2] <;> ring
  · have hp2 : p ≠ 2 := by
      intro he
      subst p
      exact hp Nat.prime_two
    simp [hp, hp2]

/-- Exact finite identity at the inclusive public cutoff, with the prime two included. -/
theorem cubic_euler_product_eq_reciprocal_partial
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0)
    (Q : ℕ) (hQ : 2 ≤ Q) :
    (∏ p ∈ Nat.primesBelow (Q + 1), ∑' k : ℕ, h (p ^ k)) =
      1 / (2 * TaoFivePrimes.twinPrimePartial Q) := by
  have he :
      (∏ p ∈ Nat.primesBelow (Q + 1), ∑' k : ℕ, h (p ^ k)) *
        TaoFivePrimes.twinPrimePartial Q = (1 / 2 : ℝ) := by
    rw [Nat.primesBelow_eq_filter_range, Finset.prod_filter,
      TaoFivePrimes.twinPrimePartial, ← Finset.prod_mul_distrib]
    calc
      _ = ∏ p ∈ Finset.range (Q + 1), if p = 2 then (1 / 2 : ℝ) else 1 := by
        apply Finset.prod_congr rfl
        intro p hp
        exact cubic_signed_prime_factor_cancellation h hmul hpv hpz p
      _ = 1 / 2 := by
        rw [Finset.prod_ite_eq']
        simp only [Finset.mem_range, show 2 < Q + 1 by omega, if_true]
  have hpos : 0 < TaoFivePrimes.twinPrimePartial Q := by
    have hbound := (TaoFivePrimes.twinPrimePartial_bounds Q).1
    linarith
  apply (eq_div_iff (by positivity : (2 : ℝ) * TaoFivePrimes.twinPrimePartial Q ≠ 0)).mpr
  nlinarith [he]

/-- The signed total mass of the same cubic coefficient is the reciprocal of
the exact public twin-prime constant. Convergence follows from its prime values. -/
theorem hasSum_reciprocal_twinPrimeConstant_of_cubic_prime_power_values
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    HasSum (fun n : ℕ => h n) (1 / TaoFivePrimes.twinPrimeConstant) := by
  have hw := weighted_summable_of_cubic_prime_power_values h hmul hpv hpz
  have hn : Summable (fun n : ℕ => ‖h n‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg (h n)) _ hw
    intro n
    by_cases hn0 : n = 0
    · subst n
      simp
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have hpow : 1 ≤ (n : ℝ)^(2 / 5 : ℝ) :=
        Real.one_le_rpow hn1 (by norm_num)
      simpa only [Real.norm_eq_abs, mul_one] using
        mul_le_mul_of_nonneg_left hpow (abs_nonneg (h n))
  have hEuler := hmul.eulerProduct hn
  have hEulerShift :
      Tendsto (fun Q : ℕ => ∏ p ∈ Nat.primesBelow (Q + 1), ∑' k : ℕ, h (p ^ k))
        atTop (𝓝 (∑' n : ℕ, h n)) :=
    (tendsto_add_atTop_iff_nat 1).mpr hEuler
  have hevent :
      (fun Q : ℕ => ∏ p ∈ Nat.primesBelow (Q + 1), ∑' k : ℕ, h (p ^ k)) =ᶠ[atTop]
        (fun Q : ℕ => 1 / (2 * TaoFivePrimes.twinPrimePartial Q)) := by
    exact Filter.eventually_atTop.mpr ⟨2, fun Q hQ =>
      cubic_euler_product_eq_reciprocal_partial h hmul hpv hpz Q hQ⟩
  have hCpos : 0 < TaoFivePrimes.twinPrimeConstant := by
    have hC := TaoFivePrimes.twinPrimeConstant_bounds.1
    linarith
  have hinv :
      Tendsto (fun Q : ℕ => 1 / (2 * TaoFivePrimes.twinPrimePartial Q)) atTop
        (𝓝 (1 / TaoFivePrimes.twinPrimeConstant)) := by
    unfold TaoFivePrimes.twinPrimeConstant at hCpos ⊢
    exact tendsto_const_nhds.div
      (tendsto_const_nhds.mul TaoFivePrimes.twinPrimePartial_tendsto_sInf) hCpos.ne'
  have hmass : (∑' n : ℕ, h n) = 1 / TaoFivePrimes.twinPrimeConstant :=
    tendsto_nhds_unique (hEulerShift.congr' hevent) hinv
  exact hmass ▸ hn.of_norm.hasSum

end PrimePairConvolution




set_option autoImplicit false

namespace PrimePairConvolution

/-!
Private analytic infrastructure for the cubic sieve correction. A positive
power moment controls every logarithmic moment. This is the elementary
logarithm-versus-power comparison used to justify the moment expansion in
Riesel--Vaughan (1983), equations (3.6)--(3.10), without differentiating an
infinite product. No coefficient-specific moment value is asserted here.
-/

theorem logPower_norm_summable_of_weighted_summable
    (h : ArithmeticFunction ℝ) (α : ℝ) (hα : 0 < α)
    (hw : Summable (fun n : ℕ => |h n| * (n : ℝ)^α)) (k : ℕ) :
    Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)^k‖) := by
  by_cases hk : k = 0
  · subst k
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hw
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hp := Real.one_le_rpow hn1 hα.le
      simpa only [pow_zero, mul_one, Real.norm_eq_abs] using
        mul_le_mul_of_nonneg_left hp (abs_nonneg (h n))
  · have hkR : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
    let β : ℝ := α / k
    have hβ : 0 < β := div_pos hα hkR
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _
      (hw.mul_left (1 / β^k))
    intro n
    by_cases hn : n = 0
    · subst n
      simp
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
      have hlog := Real.log_natCast_le_rpow_div n hβ
      have hpow := pow_le_pow_left₀ hlog0 hlog k
      have hexp : β * (k : ℝ) = α := div_mul_cancel₀ α hkR.ne'
      have hpowEq : ((n : ℝ)^β / β)^k = (n : ℝ)^α / β^k := by
        rw [div_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg n), hexp]
      rw [hpowEq] at hpow
      calc
        ‖h n * Real.log (n : ℝ)^k‖ = |h n| * Real.log (n : ℝ)^k := by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_nonneg (pow_nonneg hlog0 k)]
        _ ≤ |h n| * ((n : ℝ)^α / β^k) :=
          mul_le_mul_of_nonneg_left hpow (abs_nonneg (h n))
        _ = (1 / β^k) * (|h n| * (n : ℝ)^α) := by ring

end PrimePairConvolution




set_option autoImplicit false
open scoped BigOperators Topology
open Filter

namespace PrimePairConvolution

/-!
Exact finite Euler logarithmic moments for non-unit local masses. The generic
insertion proof is adapted from the checked RamareAnalytic.LogarithmicMoment
development; both mass factors are retained rather than simplified to one.

The actual cubic specialization follows Riesel--Vaughan (1983), (2.5)--(2.6)
and (3.9)--(3.10), pp.46,50--51. Their Dirichlet-series derivative has the
opposite sign to the coefficient logarithmic moment proved here.

This bounded stage assumes explicit norm and logarithmic norm summability.
It proves no infinite prime-series limit and uses no differentiation of an
infinite product.
-/

private theorem factored_mass_product
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (M : ℕ → ℝ)
    (hlocal : ∀ p : ℕ, p.Prime → HasSum (fun k : ℕ => h (p^k)) (M p))
    (hnorm : Summable (fun n : ℕ => ‖h n‖)) (s : Finset ℕ) :
    HasSum (fun m : Nat.factoredNumbers s => h (m : ℕ))
      (∏ p ∈ s with p.Prime, M p) := by
  have hs := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    hmul.1 hmul.2
    (fun hp => hnorm.comp_injective (Nat.pow_right_injective hp.one_lt)) s).2
  have he : (∏ p ∈ s with p.Prime, ∑' k : ℕ, h (p^k)) =
      ∏ p ∈ s with p.Prime, M p := by
    apply Finset.prod_congr rfl
    intro p hp
    exact (hlocal p (Finset.mem_filter.mp hp).2).tsum_eq
  exact he ▸ hs

set_option maxHeartbeats 800000 in
/-- Finite Euler logarithmic moments with the actual product of local masses.
No local mass is assumed to be one, positive, or nonzero; no division is used. -/
theorem factored_logarithmic_moment_product
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (M R : ℕ → ℝ)
    (hlocal : ∀ p : ℕ, p.Prime → HasSum (fun k : ℕ => h (p^k)) (M p))
    (hlocalLog : ∀ p : ℕ, p.Prime →
      HasSum (fun k : ℕ => h (p^k) * Real.log ((p^k : ℕ) : ℝ)) (M p * R p))
    (hnorm : Summable (fun n : ℕ => ‖h n‖))
    (hlognorm : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)‖))
    (s : Finset ℕ) :
    HasSum (fun m : Nat.factoredNumbers s => h (m : ℕ) * Real.log (m : ℝ))
      ((∏ p ∈ s with p.Prime, M p) * (∑ p ∈ s with p.Prime, R p)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Nat.factoredNumbers_empty]
    simp only [Finset.filter_empty, Finset.sum_empty, Finset.prod_empty, mul_zero]
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
      rw [Finset.filter_insert, if_pos hp, Finset.prod_insert hpfilter,
        Finset.sum_insert hpfilter,
        ← (Nat.equivProdNatFactoredNumbers hp hps).hasSum_iff, Function.comp_def]
      have hnp : Summable (fun k : ℕ => ‖h (p^k)‖) :=
        hnorm.comp_injective (Nat.pow_right_injective hp.one_lt)
      have hlp : Summable (fun k : ℕ => ‖h (p^k) * Real.log ((p^k : ℕ) : ℝ)‖) :=
        hlognorm.comp_injective (Nat.pow_right_injective hp.one_lt)
      have hns : Summable (fun m : Nat.factoredNumbers s => ‖h (m : ℕ)‖) :=
        hnorm.subtype (Nat.factoredNumbers s)
      have hls : Summable (fun m : Nat.factoredNumbers s =>
          ‖h (m : ℕ) * Real.log (m : ℝ)‖) :=
        hlognorm.subtype (Nat.factoredNumbers s)
      have hprod_left : Summable (fun x : ℕ × Nat.factoredNumbers s =>
          (h (p^x.1) * Real.log ((p^x.1 : ℕ) : ℝ)) * h (x.2 : ℕ)) :=
        summable_mul_of_summable_norm hlp hns
      have hprod_right : Summable (fun x : ℕ × Nat.factoredNumbers s =>
          h (p^x.1) * (h (x.2 : ℕ) * Real.log (x.2 : ℝ))) :=
        summable_mul_of_summable_norm hnp hls
      have hleft := (hlocalLog p hp).mul
        (factored_mass_product h hmul M hlocal hnorm s) hprod_left
      have hright := (hlocal p hp).mul ih hprod_right
      have hjoined := hleft.add hright
      have he : (M p * R p) * (∏ q ∈ s with q.Prime, M q) +
          M p * ((∏ q ∈ s with q.Prime, M q) * (∑ q ∈ s with q.Prime, R q)) =
          (M p * (∏ q ∈ s with q.Prime, M q)) *
            (R p + (∑ q ∈ s with q.Prime, R q)) := by ring
      rw [he] at hjoined
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

/-- The complete signed local Euler factor of the actual cubic correction. -/
noncomputable def cubicEulerMass (p : ℕ) : ℝ :=
  (1 + (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2))) *
    (1 - 1 / (p : ℝ))^2

/-- Local logarithmic moment divided by the local mass, on prime inputs. -/
noncomputable def cubicEulerLogRatio (p : ℕ) : ℝ :=
  if p = 2 then -(3 / 2 : ℝ) * Real.log 2
  else -(2 * Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)))

private theorem cubic_local_mass
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (p : ℕ) (hp : p.Prime)
    (hpv : h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ k : ℕ, 4 ≤ k → h (p^k) = 0) :
    HasSum (fun k : ℕ => h (p^k)) (cubicEulerMass p) := by
  have hs := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := Finset.range 4) (f := fun k => h (p^k)) (by
      intro k hk
      exact hpz k (by simpa only [Finset.mem_range, not_lt] using hk))
  have he : (∑ k ∈ Finset.range 4, h (p^k)) = cubicEulerMass p := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, hmul.1, hpv.1, hpv.2.1, hpv.2.2, cubicEulerMass]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
    field_simp [hp0] <;> ring
  exact he ▸ hs

private theorem cubic_local_log_mass
    (h : ArithmeticFunction ℝ) (p : ℕ) (hp : p.Prime)
    (hpv : h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ k : ℕ, 4 ≤ k → h (p^k) = 0) :
    HasSum (fun k : ℕ => h (p^k) * Real.log ((p^k : ℕ) : ℝ))
      (cubicEulerMass p * cubicEulerLogRatio p) := by
  have hs := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := Finset.range 4)
    (f := fun k => h (p^k) * Real.log ((p^k : ℕ) : ℝ)) (by
      intro k hk
      rw [hpz k (by simpa only [Finset.mem_range, not_lt] using hk), zero_mul])
  have he :
      (∑ k ∈ Finset.range 4, h (p^k) * Real.log ((p^k : ℕ) : ℝ)) =
        cubicEulerMass p * cubicEulerLogRatio p := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, hpv.1, hpv.2.1, hpv.2.2, Nat.cast_one,
      Real.log_one, mul_zero, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    by_cases hp2 : p = 2
    · subst p
      norm_num [cubicEulerMass, cubicEulerLogRatio]
      <;> ring
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      have h0 : (p : ℝ) ≠ 0 := by linarith
      have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
      simp only [cubicEulerMass, cubicEulerLogRatio, if_neg hp2]
      field_simp [h0, h1, h2] <;> ring
  exact he ▸ hs

/-- Exact finite-prime-factor logarithmic moment for the actual cubic family.
Global norm hypotheses justify sums over infinitely many factored numbers;
the local masses and logarithmic factors are proved from the prime values. -/
theorem cubic_factored_logarithmic_moment
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0)
    (hnorm : Summable (fun n : ℕ => ‖h n‖))
    (hlognorm : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)‖))
    (s : Finset ℕ) :
    HasSum (fun m : Nat.factoredNumbers s => h (m : ℕ) * Real.log (m : ℝ))
      ((∏ p ∈ s with p.Prime, cubicEulerMass p) *
        (∑ p ∈ s with p.Prime, cubicEulerLogRatio p)) := by
  exact factored_logarithmic_moment_product h hmul cubicEulerMass cubicEulerLogRatio
    (fun p hp => cubic_local_mass h hmul p hp (hpv p hp) (fun k hk => hpz p k hp hk))
    (fun p hp => cubic_local_log_mass h p hp (hpv p hp) (fun k hk => hpz p k hp hk))
    hnorm hlognorm s

end PrimePairConvolution




set_option autoImplicit false
open scoped BigOperators

namespace RamareAnalytic

/-!
A discrete Chebyshev estimate for the logarithmic prime moment in
Ramare's correction constant. This file has not yet been compiled.

The analytic conclusion is derived from Mathlib's theta bound; neither
summability nor a prime-tail estimate is assumed. The last rational corollary
exposes the separate finite certificate log 4 <= 7/5 as a hypothesis.
This gives a slightly sharper tail than the integral argument in
constant_certificate_plan.md. Intended environment: Lean 4.33.1 / Mathlib
0df444a360eaa60ab8c11dca51a86af692955474.
-/

private noncomputable def reciprocalQuadratic (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * ((n : ℝ) - 1))

private noncomputable def reciprocalPair (n : ℕ) : ℝ :=
  1 / ((n : ℝ) - 1) + 1 / (n : ℝ)

private theorem reciprocalQuadratic_nonneg (n : ℕ) :
    0 ≤ reciprocalQuadratic n := by
  by_cases hn : n = 0
  · simp [hn, reciprocalQuadratic]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact one_div_nonneg.mpr (mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hn1))

private theorem reciprocalQuadratic_drop (n : ℕ) (hn : 2 ≤ n) :
    reciprocalQuadratic n - reciprocalQuadratic (n + 1) =
      2 / (((n : ℝ) - 1) * (n : ℝ) * ((n : ℝ) + 1)) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hm0 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (n : ℝ) + 1 ≠ 0 := by linarith
  simp only [reciprocalQuadratic, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  field_simp
  <;> ring

private theorem reciprocalQuadratic_drop_nonneg (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ reciprocalQuadratic n - reciprocalQuadratic (n + 1) := by
  rw [reciprocalQuadratic_drop n hn]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm : 0 ≤ (n : ℝ) - 1 := by linarith
  positivity

private theorem reciprocalQuadratic_telescope (n : ℕ) (hn : 2 ≤ n) :
    (reciprocalQuadratic n - reciprocalQuadratic (n + 1)) * (n : ℝ) =
      reciprocalPair n - reciprocalPair (n + 1) := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hm0 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (n : ℝ) + 1 ≠ 0 := by linarith
  simp only [reciprocalQuadratic, reciprocalPair, Nat.cast_add, Nat.cast_one,
    add_sub_cancel_right]
  field_simp
  <;> ring

private theorem reciprocalPair_sum (X N : ℕ) (hXN : X + 1 ≤ N) :
    (∑ i ∈ Finset.Ico (X + 1) N,
      (reciprocalPair i - reciprocalPair (i + 1))) =
      reciprocalPair (X + 1) - reciprocalPair N := by
  calc
    (∑ i ∈ Finset.Ico (X + 1) N,
        (reciprocalPair i - reciprocalPair (i + 1))) =
        -(∑ i ∈ Finset.Ico (X + 1) N,
          (reciprocalPair (i + 1) - reciprocalPair i)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = reciprocalPair (X + 1) - reciprocalPair N := by
      rw [Finset.sum_Ico_sub reciprocalPair hXN]
      ring

/-- Discrete Abel bound for a sequence vanishing up to X with linear prefix control. -/
private theorem weighted_partial_sum_le
    (a : ℕ → ℝ) (A : ℝ) (X : ℕ) (hA : 0 ≤ A) (hX : 1 ≤ X)
    (hzero : ∀ i, i ≤ X → a i = 0)
    (hprefix : ∀ N, (∑ i ∈ Finset.range (N + 1), a i) ≤ A * (N : ℝ))
    (N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), reciprocalQuadratic i * a i) ≤
      A * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) := by
  have hC : 0 ≤ A * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) := by
    positivity
  by_cases hNX : N ≤ X
  · have hz : (∑ i ∈ Finset.range (N + 1), reciprocalQuadratic i * a i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero i (by have := Finset.mem_range.mp hi; omega), mul_zero]
    simpa only [hz] using hC
  · have hXN : X + 1 ≤ N := by omega
    have hN2 : 2 ≤ N := by omega
    have hGzero : (∑ i ∈ Finset.range (X + 1), a i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hzero i (by have := Finset.mem_range.mp hi; omega)
    have hWzero : (∑ i ∈ Finset.range (X + 1), reciprocalQuadratic i * a i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hzero i (by have := Finset.mem_range.mp hi; omega), mul_zero]
    have hIco : (∑ i ∈ Finset.Ico (X + 1) (N + 1), reciprocalQuadratic i * a i) =
        ∑ i ∈ Finset.range (N + 1), reciprocalQuadratic i * a i := by
      rw [Finset.sum_Ico_eq_sub _ (by omega), hWzero, sub_zero]
    have hAbel := Finset.sum_Ico_by_parts reciprocalQuadratic a
      (show X + 1 < N + 1 by omega)
    simp only [smul_eq_mul, Nat.add_sub_cancel, hGzero, mul_zero, sub_zero, hIco] at hAbel
    have hAbel' : (∑ i ∈ Finset.range (N + 1), reciprocalQuadratic i * a i) =
        reciprocalQuadratic N * (∑ i ∈ Finset.range (N + 1), a i) +
        ∑ i ∈ Finset.Ico (X + 1) N,
          (reciprocalQuadratic i - reciprocalQuadratic (i + 1)) *
            (∑ j ∈ Finset.range (i + 1), a j) := by
      rw [hAbel, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    have hcorrection :
        (∑ i ∈ Finset.Ico (X + 1) N,
          (reciprocalQuadratic i - reciprocalQuadratic (i + 1)) *
            (∑ j ∈ Finset.range (i + 1), a j)) ≤
        A * (reciprocalPair (X + 1) - reciprocalPair N) := by
      calc
        _ ≤ ∑ i ∈ Finset.Ico (X + 1) N,
            (reciprocalQuadratic i - reciprocalQuadratic (i + 1)) * (A * (i : ℝ)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi2 : 2 ≤ i := by have := (Finset.mem_Ico.mp hi).1; omega
          exact mul_le_mul_of_nonneg_left (hprefix i)
            (reciprocalQuadratic_drop_nonneg i hi2)
        _ = A * ∑ i ∈ Finset.Ico (X + 1) N,
            (reciprocalQuadratic i - reciprocalQuadratic (i + 1)) * (i : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = A * ∑ i ∈ Finset.Ico (X + 1) N,
            (reciprocalPair i - reciprocalPair (i + 1)) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          exact reciprocalQuadratic_telescope i
            (by have := (Finset.mem_Ico.mp hi).1; omega)
        _ = _ := by rw [reciprocalPair_sum X N hXN]
    have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hN0 : (N : ℝ) ≠ 0 := by linarith
    have hNm0 : (N : ℝ) - 1 ≠ 0 := by linarith
    have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
    have hXp0 : (X : ℝ) + 1 ≠ 0 := by positivity
    calc
      _ = _ := hAbel'
      _ ≤ reciprocalQuadratic N * (A * (N : ℝ)) +
          A * (reciprocalPair (X + 1) - reciprocalPair N) :=
        add_le_add (mul_le_mul_of_nonneg_left (hprefix N)
          (reciprocalQuadratic_nonneg N)) hcorrection
      _ = A * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) - A / (N : ℝ) := by
        simp only [reciprocalQuadratic, reciprocalPair, Nat.cast_add, Nat.cast_one,
          add_sub_cancel_right]
        field_simp
        <;> ring
      _ ≤ _ := sub_le_self _ (div_nonneg hA (Nat.cast_nonneg N))

/-- A bounded-prefix argument establishes convergence before taking the infinite bound. -/
theorem summable_weighted_tail_of_prefix_le
    (a : ℕ → ℝ) (A : ℝ) (X : ℕ) (hA : 0 ≤ A) (hX : 1 ≤ X)
    (ha : ∀ i, 0 ≤ a i) (hzero : ∀ i, i ≤ X → a i = 0)
    (hprefix : ∀ N, (∑ i ∈ Finset.range (N + 1), a i) ≤ A * (N : ℝ)) :
    Summable (fun i => a i / ((i : ℝ) * ((i : ℝ) - 1))) ∧
      (∑' i, a i / ((i : ℝ) * ((i : ℝ) - 1))) ≤
        A * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) := by
  have hpos : ∀ i, 0 ≤ reciprocalQuadratic i * a i :=
    fun i => mul_nonneg (reciprocalQuadratic_nonneg i) (ha i)
  have hbound : ∀ N, (∑ i ∈ Finset.range N, reciprocalQuadratic i * a i) ≤
      A * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) := by
    intro N
    cases N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; positivity
    | succ N => exact weighted_partial_sum_le a A X hA hX hzero hprefix N
  have hs := summable_of_sum_range_le hpos hbound
  have hb := Real.tsum_le_of_sum_range_le hpos hbound
  simpa only [reciprocalQuadratic, div_eq_mul_inv, one_mul, mul_comm] using And.intro hs hb

noncomputable def primeLogAfter (X n : ℕ) : ℝ :=
  if X < n ∧ n.Prime then Real.log (n : ℝ) else 0

theorem primeLogAfter_nonneg (X n : ℕ) : 0 ≤ primeLogAfter X n := by
  unfold primeLogAfter
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.2.one_lt.le)
  · exact le_rfl

theorem primeLogAfter_prefix_le (X N : ℕ) :
    (∑ i ∈ Finset.range (N + 1), primeLogAfter X i) ≤ Real.log 4 * (N : ℝ) := by
  calc
    _ ≤ ∑ i ∈ Finset.range (N + 1), if i.Prime then Real.log (i : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hp : i.Prime
      · have hlog : 0 ≤ Real.log (i : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
        by_cases hXi : X < i <;> simp [primeLogAfter, hXi, hp, hlog]
      · simp [primeLogAfter, hp]
    _ = Chebyshev.theta (N : ℝ) := by
      rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast,
        ← Nat.range_succ_eq_Icc_zero, Finset.sum_filter]
    _ ≤ _ := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N)

/-- The exact prime logarithmic-moment tail needed for Ramare's constant. -/
theorem prime_log_moment_tail (X : ℕ) (hX : 1 ≤ X) :
    Summable (fun p : ℕ =>
      if X < p ∧ p.Prime then Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ∧
    (∑' p : ℕ, if X < p ∧ p.Prime then
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ≤
      Real.log 4 * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) := by
  have h := summable_weighted_tail_of_prefix_le
    (primeLogAfter X) (Real.log 4) X (Real.log_nonneg (by norm_num)) hX
    (primeLogAfter_nonneg X)
    (fun i hi => by simp [primeLogAfter, not_lt_of_ge hi])
    (primeLogAfter_prefix_le X)
  simpa only [primeLogAfter, ite_div, zero_div] using h

/-- Rational specialization; the remaining log(4) premise has an independent finite certificate. -/
theorem prime_log_moment_tail_1000 (hlog4 : Real.log 4 ≤ (7 / 5 : ℝ)) :
    (∑' p : ℕ, if 1000 < p ∧ p.Prime then
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ≤ (14 / 4995 : ℝ) := by
  have h := (prime_log_moment_tail 1000 (by omega)).2
  calc
    _ ≤ Real.log 4 * (1 / (1000 : ℝ) + 1 / ((1000 : ℝ) + 1)) := h
    _ ≤ (7 / 5 : ℝ) * (1 / (1000 : ℝ) + 1 / ((1000 : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_right hlog4 (by norm_num)
    _ ≤ _ := by norm_num

end RamareAnalytic



/-!
Passage from finite Euler logarithmic moments to the actual infinite moment.
This fragment follows CubicLogarithmicMoment, BaseCorrectionMass,
WeightedLogMoments and PrimeLogTail in one assembled source.

The sign is the negative of the Dirichlet-series derivative in
Riesel--Vaughan (1983), (3.10). No infinite product is differentiated.
-/

open scoped BigOperators Topology
open Filter

namespace PrimePairConvolution

/-- Exhaustion by finite sets of allowed prime factors recovers an absolutely
convergent arithmetic series. The zero term must vanish. -/
private theorem factored_tsum_tendsto
    (f : ℕ → ℝ) (hf : Summable f) (hf0 : f 0 = 0) :
    Tendsto (fun s : Finset ℕ => ∑' m : Nat.factoredNumbers s, f (m : ℕ))
      atTop (𝓝 (∑' n : ℕ, f n)) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := EulerProduct.norm_tsum_factoredNumbers_sub_tsum_lt hf hf0 hε
  refine ⟨Finset.range N, fun s hs => ?_⟩
  rw [dist_eq_norm, norm_sub_rev]
  apply hN s
  intro p hp
  exact hs (Finset.mem_range.mpr (Nat.lt_of_mem_primesBelow hp))

/-- An infinite logarithmic moment from local Euler sums and the finite
product-mass identity. Both limiting sums are explicit `HasSum` inputs. -/
theorem hasSum_logarithmic_moment_of_local_euler
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (M R : ℕ → ℝ) (mass ratioSum : ℝ)
    (hlocal : ∀ p : ℕ, p.Prime → HasSum (fun k : ℕ => h (p^k)) (M p))
    (hlocalLog : ∀ p : ℕ, p.Prime →
      HasSum (fun k : ℕ => h (p^k) * Real.log ((p^k : ℕ) : ℝ)) (M p * R p))
    (hnorm : Summable (fun n : ℕ => ‖h n‖))
    (hlognorm : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)‖))
    (hmass : HasSum (fun n : ℕ => h n) mass)
    (hratio : HasSum (fun p : Nat.Primes => R (p : ℕ)) ratioSum) :
    HasSum (fun n : ℕ => h n * Real.log (n : ℝ)) (mass * ratioSum) := by
  classical
  have hm : Tendsto
      (fun s : Finset ℕ => ∏ p ∈ s with p.Prime, M p)
      atTop (𝓝 mass) := by
    have ht := factored_tsum_tendsto (fun n => h n) hnorm.of_norm (by simp)
    rw [hmass.tsum_eq] at ht
    apply ht.congr
    intro s
    exact (factored_mass_product h hmul M hlocal hnorm s).tsum_eq
  have hr : Tendsto
      (fun s : Finset ℕ => ∑ p ∈ s with p.Prime, R p)
      atTop (𝓝 ratioSum) := by
    change HasSum (R ∘ Subtype.val (p := (· ∈ {p | Nat.Prime p}))) ratioSum at hratio
    rw [hasSum_subtype_iff_indicator] at hratio
    change Tendsto
      (fun s : Finset ℕ => ∑ p ∈ s, Set.indicator {p | Nat.Prime p} R p)
      atTop (𝓝 ratioSum) at hratio
    apply hratio.congr
    intro s
    exact Finset.sum_indicator_eq_sum_filter s (fun _ => R) _ id
  have hprod : Tendsto
      (fun s : Finset ℕ => ∑' m : Nat.factoredNumbers s,
        h (m : ℕ) * Real.log (m : ℝ)) atTop (𝓝 (mass * ratioSum)) := by
    apply (hm.mul hr).congr
    intro s
    exact (factored_logarithmic_moment_product h hmul M R hlocal hlocalLog
      hnorm hlognorm s).tsum_eq.symm
  have hvalue : (∑' n : ℕ, h n * Real.log (n : ℝ)) = mass * ratioSum :=
    tendsto_nhds_unique
      (factored_tsum_tendsto (fun n => h n * Real.log (n : ℝ))
        hlognorm.of_norm (by simp)) hprod
  exact hvalue ▸ hlognorm.of_norm.hasSum

/-- The known prime-log tail at cutoff one covers every prime, and hence
supplies actual convergence of the full prime logarithmic series. -/
theorem summable_prime_log_quotient :
    Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) := by
  classical
  let g : ℕ → ℝ := fun p => Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
  change Summable (g ∘ Subtype.val (p := (· ∈ {p | Nat.Prime p})))
  rw [summable_subtype_iff_indicator]
  have ht := (RamareAnalytic.prime_log_moment_tail 1 (by norm_num)).1
  apply ht.congr
  intro p
  by_cases hp : p.Prime
  · simp [Set.indicator, g, hp, hp.one_lt]
  · simp [Set.indicator, g, hp]

/-- The prime two contributes the additional negative half-logarithm beyond
twice the usual prime-log series. No coefficient moment is assumed. -/
theorem cubic_log_ratio_hasSum
    (A : ℝ)
    (hA : HasSum (fun p : Nat.Primes =>
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) A) :
    HasSum (fun p : Nat.Primes => cubicEulerLogRatio (p : ℕ))
      (-(2 * A + Real.log 2 / 2)) := by
  classical
  let g : ℕ → ℝ := fun p => Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))
  change HasSum (g ∘ Subtype.val (p := (· ∈ {p | Nat.Prime p}))) A at hA
  rw [hasSum_subtype_iff_indicator] at hA
  have hdelta : HasSum (fun p : ℕ => if p = 2 then Real.log 2 / 2 else 0)
      (Real.log 2 / 2) := hasSum_ite_eq 2 (Real.log 2 / 2)
  have hr := (hA.mul_left (-2)).sub hdelta
  have hval : (-2 : ℝ) * A - Real.log 2 / 2 = -(2 * A + Real.log 2 / 2) := by ring
  rw [hval] at hr
  change HasSum
    (cubicEulerLogRatio ∘ Subtype.val (p := (· ∈ {p | Nat.Prime p}))) _
  rw [hasSum_subtype_iff_indicator]
  apply hr.congr_fun
  intro p
  by_cases hp : p.Prime
  · by_cases hp2 : p = 2
    · subst p
      norm_num [Set.indicator, g, cubicEulerLogRatio, Nat.prime_two]
      <;> ring
    · simp [Set.indicator, hp, cubicEulerLogRatio, hp2, g]
      ring
  · have hp2 : p ≠ 2 := by
      intro he
      subst p
      exact hp Nat.prime_two
    simp [Set.indicator, hp, hp2]

/-- The actual first logarithmic moment of the common cubic coefficient.
Convergence is derived from its prime-power values and the passed weighted
moment; no convergence or coefficient-moment identity is assumed. -/
theorem cubic_logarithmic_moment_hasSum
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    HasSum (fun n : ℕ => h n * Real.log (n : ℝ))
      (-((2 * (∑' p : Nat.Primes,
        Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2) /
          TaoFivePrimes.twinPrimeConstant)) := by
  have hw := weighted_summable_of_cubic_prime_power_values h hmul hpv hpz
  have hn : Summable (fun n : ℕ => ‖h n‖) := by
    simpa only [pow_zero, mul_one] using
      logPower_norm_summable_of_weighted_summable h (2 / 5) (by norm_num) hw 0
  have hl : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)‖) := by
    simpa only [pow_one] using
      logPower_norm_summable_of_weighted_summable h (2 / 5) (by norm_num) hw 1
  have hm := hasSum_reciprocal_twinPrimeConstant_of_cubic_prime_power_values
    h hmul hpv hpz
  have hr := cubic_log_ratio_hasSum _ summable_prime_log_quotient.hasSum
  have hfull := hasSum_logarithmic_moment_of_local_euler
    h hmul cubicEulerMass cubicEulerLogRatio _ _
    (fun p hp => cubic_local_mass h hmul p hp (hpv p hp) (fun k hk => hpz p k hp hk))
    (fun p hp => cubic_local_log_mass h p hp (hpv p hp) (fun k hk => hpz p k hp hk))
    hn hl hm hr
  convert hfull using 1 <;> ring

end PrimePairConvolution



/-!
Finite Euler second logarithmic moments, retaining the actual local masses.
This fragment follows the passed CubicLogarithmicMoment body in the same file.

The signed local variance is an algebraic cumulant, not a nonnegative
probabilistic variance. For the actual cubic coefficient it is negative.
The exceptional prime-two correction agrees with Riesel--Vaughan (1983),
printed p.51: the correction to the negative all-prime D-sum is +log(2)^2/4.

This finite-prime stage assumes the three explicit absolute summability
premises needed to justify its factored-number sums. It neither assumes nor
proves the final infinite second-moment formula. No infinite product is
differentiated.
-/

open scoped BigOperators Topology

namespace PrimePairConvolution

set_option maxHeartbeats 1000000 in
/-- Finite Euler second moments. The local second moment is parametrized as
`M p * (R p ^ 2 + V p)`, so no nonzero or positive mass premise is required. -/
theorem factored_second_logarithmic_moment_product
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (M R V : ℕ → ℝ)
    (hlocal : ∀ p : ℕ, p.Prime → HasSum (fun k : ℕ => h (p^k)) (M p))
    (hlocalLog : ∀ p : ℕ, p.Prime →
      HasSum (fun k : ℕ => h (p^k) * Real.log ((p^k : ℕ) : ℝ)) (M p * R p))
    (hlocalLogSq : ∀ p : ℕ, p.Prime →
      HasSum (fun k : ℕ => h (p^k) * Real.log ((p^k : ℕ) : ℝ)^2)
        (M p * ((R p)^2 + V p)))
    (hnorm : Summable (fun n : ℕ => ‖h n‖))
    (hlognorm : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)‖))
    (hlogSqnorm : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)^2‖))
    (s : Finset ℕ) :
    HasSum (fun m : Nat.factoredNumbers s => h (m : ℕ) * Real.log (m : ℝ)^2)
      ((∏ p ∈ s with p.Prime, M p) *
        ((∑ p ∈ s with p.Prime, R p)^2 + (∑ p ∈ s with p.Prime, V p))) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Nat.factoredNumbers_empty]
    simp only [Finset.filter_empty, Finset.sum_empty, Finset.prod_empty,
      zero_pow (by decide : 2 ≠ 0), zero_add, mul_zero]
    have hz : HasSum (fun _ : ({1} : Set ℕ) => (0 : ℝ)) 0 := hasSum_zero
    apply hz.congr_fun
    intro m
    have hm : (m : ℕ) = 1 := Set.mem_singleton_iff.mp m.property
    simp only [hm, Nat.cast_one, Real.log_one, zero_pow (by decide : 2 ≠ 0), mul_zero]
  | @insert p s hps ih =>
    by_cases hp : p.Prime
    · have hpfilter : p ∉ {q ∈ s | q.Prime} := by
        intro hh
        exact hps (Finset.mem_filter.mp hh).1
      simp only [Finset.filter_insert, if_pos hp, Finset.prod_insert hpfilter,
        Finset.sum_insert hpfilter]
      rw [← (Nat.equivProdNatFactoredNumbers hp hps).hasSum_iff, Function.comp_def]
      have hnp : Summable (fun k : ℕ => ‖h (p^k)‖) :=
        hnorm.comp_injective (Nat.pow_right_injective hp.one_lt)
      have hlp : Summable (fun k : ℕ => ‖h (p^k) * Real.log ((p^k : ℕ) : ℝ)‖) :=
        hlognorm.comp_injective (Nat.pow_right_injective hp.one_lt)
      have hl2p : Summable (fun k : ℕ => ‖h (p^k) * Real.log ((p^k : ℕ) : ℝ)^2‖) :=
        hlogSqnorm.comp_injective (Nat.pow_right_injective hp.one_lt)
      have hns : Summable (fun m : Nat.factoredNumbers s => ‖h (m : ℕ)‖) :=
        hnorm.subtype (Nat.factoredNumbers s)
      have hls : Summable (fun m : Nat.factoredNumbers s =>
          ‖h (m : ℕ) * Real.log (m : ℝ)‖) :=
        hlognorm.subtype (Nat.factoredNumbers s)
      have hl2s : Summable (fun m : Nat.factoredNumbers s =>
          ‖h (m : ℕ) * Real.log (m : ℝ)^2‖) :=
        hlogSqnorm.subtype (Nat.factoredNumbers s)
      have hprod_left : Summable (fun x : ℕ × Nat.factoredNumbers s =>
          (h (p^x.1) * Real.log ((p^x.1 : ℕ) : ℝ)^2) * h (x.2 : ℕ)) :=
        summable_mul_of_summable_norm hl2p hns
      have hprod_cross : Summable (fun x : ℕ × Nat.factoredNumbers s =>
          (h (p^x.1) * Real.log ((p^x.1 : ℕ) : ℝ)) *
            (h (x.2 : ℕ) * Real.log (x.2 : ℝ))) :=
        summable_mul_of_summable_norm hlp hls
      have hprod_right : Summable (fun x : ℕ × Nat.factoredNumbers s =>
          h (p^x.1) * (h (x.2 : ℕ) * Real.log (x.2 : ℝ)^2)) :=
        summable_mul_of_summable_norm hnp hl2s
      have hleft := (hlocalLogSq p hp).mul
        (factored_mass_product h hmul M hlocal hnorm s) hprod_left
      have hcross := (hlocalLog p hp).mul
        (factored_logarithmic_moment_product h hmul M R hlocal hlocalLog
          hnorm hlognorm s) hprod_cross
      have hright := (hlocal p hp).mul ih hprod_right
      have hjoined := (hleft.add (hcross.mul_left (2 : ℝ))).add hright
      have he :
          (M p * ((R p)^2 + V p)) * (∏ q ∈ s with q.Prime, M q) +
            2 * ((M p * R p) *
              ((∏ q ∈ s with q.Prime, M q) * (∑ q ∈ s with q.Prime, R q))) +
            M p * ((∏ q ∈ s with q.Prime, M q) *
              ((∑ q ∈ s with q.Prime, R q)^2 + (∑ q ∈ s with q.Prime, V q))) =
          (M p * (∏ q ∈ s with q.Prime, M q)) *
            ((R p + (∑ q ∈ s with q.Prime, R q))^2 +
              (V p + (∑ q ∈ s with q.Prime, V q))) := by ring
      rw [he] at hjoined
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

/-- The nonnegative all-prime term in the source's second logarithmic constant.
Its sign is reversed in the local signed variance. -/
noncomputable def cubicSecondPrimeTerm (p : ℕ) : ℝ :=
  (8*(p : ℝ)^2 - 10*(p : ℝ) + 4) / ((p : ℝ)^2 * ((p : ℝ)-1)^2) *
    Real.log (p : ℝ)^2

/-- Signed normalized local second moment minus the squared local first ratio. -/
noncomputable def cubicEulerLogVariance (p : ℕ) : ℝ :=
  if p = 2 then -(15 / 4 : ℝ) * Real.log 2^2 else -cubicSecondPrimeTerm p

/-- The exceptional contribution is one quarter, not one half. This is a
pointwise algebraic identity and assumes no infinite-series convergence. -/
theorem cubicEulerLogVariance_eq_correction_sub (p : ℕ) :
    cubicEulerLogVariance p =
      (if p = 2 then (1 / 4 : ℝ) * Real.log 2^2 else 0) - cubicSecondPrimeTerm p := by
  by_cases hp2 : p = 2
  · subst p
    norm_num [cubicEulerLogVariance, cubicSecondPrimeTerm]
    <;> ring
  · simp only [cubicEulerLogVariance, if_neg hp2, zero_sub]

private theorem cubic_local_log_squared_mass
    (h : ArithmeticFunction ℝ) (p : ℕ) (hp : p.Prime)
    (hpv : h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ k : ℕ, 4 ≤ k → h (p^k) = 0) :
    HasSum (fun k : ℕ => h (p^k) * Real.log ((p^k : ℕ) : ℝ)^2)
      (cubicEulerMass p * ((cubicEulerLogRatio p)^2 + cubicEulerLogVariance p)) := by
  have hs := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := Finset.range 4)
    (f := fun k => h (p^k) * Real.log ((p^k : ℕ) : ℝ)^2) (by
      intro k hk
      rw [hpz k (by simpa only [Finset.mem_range, not_lt] using hk), zero_mul])
  have he :
      (∑ k ∈ Finset.range 4, h (p^k) * Real.log ((p^k : ℕ) : ℝ)^2) =
        cubicEulerMass p * ((cubicEulerLogRatio p)^2 + cubicEulerLogVariance p) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one, hpv.1, hpv.2.1, hpv.2.2, Nat.cast_one,
      Real.log_one, zero_pow (by decide : 2 ≠ 0), mul_zero,
      Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
    by_cases hp2 : p = 2
    · subst p
      norm_num [cubicEulerMass, cubicEulerLogRatio, cubicEulerLogVariance]
      <;> ring
    · have hp3 : 3 ≤ p := by have := hp.two_le; omega
      have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
      have h0 : (p : ℝ) ≠ 0 := by linarith
      have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
      simp only [cubicEulerMass, cubicEulerLogRatio, cubicEulerLogVariance,
        cubicSecondPrimeTerm, if_neg hp2]
      field_simp [h0, h1, h2] <;> ring
  exact he ▸ hs

/-- Exact finite Euler second moment for the same actual cubic coefficient.
The three absolute summability premises justify the infinite factored-number
sums; the local values and the quarter-log-two correction are proved. -/
theorem cubic_factored_second_logarithmic_moment
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0)
    (hnorm : Summable (fun n : ℕ => ‖h n‖))
    (hlognorm : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)‖))
    (hlogSqnorm : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)^2‖))
    (s : Finset ℕ) :
    HasSum (fun m : Nat.factoredNumbers s => h (m : ℕ) * Real.log (m : ℝ)^2)
      ((∏ p ∈ s with p.Prime, cubicEulerMass p) *
        ((∑ p ∈ s with p.Prime, cubicEulerLogRatio p)^2 +
          (∑ p ∈ s with p.Prime, cubicEulerLogVariance p))) := by
  exact factored_second_logarithmic_moment_product h hmul
    cubicEulerMass cubicEulerLogRatio cubicEulerLogVariance
    (fun p hp => cubic_local_mass h hmul p hp (hpv p hp) (fun k hk => hpz p k hp hk))
    (fun p hp => cubic_local_log_mass h p hp (hpv p hp) (fun k hk => hpz p k hp hk))
    (fun p hp => cubic_local_log_squared_mass h p hp (hpv p hp)
      (fun k hk => hpz p k hp hk))
    hnorm hlognorm hlogSqnorm s

end PrimePairConvolution



/-!
Infinite second logarithmic moment for the actual cubic correction.
This fragment follows the passed first-moment limit assembly and the separate
finite second-moment fragment, without duplicating their common parent.

The prime D-series convergence is proved by D_p <= 512*p^(-3/2). Coefficient
log-square convergence follows from the already proved positive-power moment.
No convergence or second-moment identity is assumed in the final theorem.
-/

open scoped BigOperators Topology
open Filter

namespace PrimePairConvolution

private theorem prime_filtered_tendsto_of_hasSum
    (f : ℕ → ℝ) (a : ℝ)
    (ha : HasSum (fun p : Nat.Primes => f (p : ℕ)) a) :
    Tendsto (fun s : Finset ℕ => ∑ p ∈ s with p.Prime, f p) atTop (𝓝 a) := by
  classical
  change HasSum (f ∘ Subtype.val (p := (· ∈ {p | Nat.Prime p}))) a at ha
  rw [hasSum_subtype_iff_indicator] at ha
  change Tendsto
    (fun s : Finset ℕ => ∑ p ∈ s, Set.indicator {p | Nat.Prime p} f p)
    atTop (𝓝 a) at ha
  apply ha.congr
  intro s
  exact Finset.sum_indicator_eq_sum_filter s (fun _ => f) _ id

/-- Passage from finite Euler second moments to an actual coefficient HasSum.
The local-series and prime-series inputs are explicit; the conclusion is not
assumed as a convergence or value premise. -/
theorem hasSum_second_logarithmic_moment_of_local_euler
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (M R V : ℕ → ℝ) (mass ratioSum varianceSum : ℝ)
    (hlocal : ∀ p : ℕ, p.Prime → HasSum (fun k : ℕ => h (p^k)) (M p))
    (hlocalLog : ∀ p : ℕ, p.Prime →
      HasSum (fun k : ℕ => h (p^k) * Real.log ((p^k : ℕ) : ℝ)) (M p * R p))
    (hlocalLogSq : ∀ p : ℕ, p.Prime →
      HasSum (fun k : ℕ => h (p^k) * Real.log ((p^k : ℕ) : ℝ)^2)
        (M p * ((R p)^2 + V p)))
    (hnorm : Summable (fun n : ℕ => ‖h n‖))
    (hlognorm : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)‖))
    (hlogSqnorm : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)^2‖))
    (hmass : HasSum (fun n : ℕ => h n) mass)
    (hratio : HasSum (fun p : Nat.Primes => R (p : ℕ)) ratioSum)
    (hvariance : HasSum (fun p : Nat.Primes => V (p : ℕ)) varianceSum) :
    HasSum (fun n : ℕ => h n * Real.log (n : ℝ)^2)
      (mass * (ratioSum^2 + varianceSum)) := by
  classical
  have hm : Tendsto
      (fun s : Finset ℕ => ∏ p ∈ s with p.Prime, M p)
      atTop (𝓝 mass) := by
    have ht := factored_tsum_tendsto (fun n => h n) hnorm.of_norm (by simp)
    rw [hmass.tsum_eq] at ht
    apply ht.congr
    intro s
    exact (factored_mass_product h hmul M hlocal hnorm s).tsum_eq
  have hr := prime_filtered_tendsto_of_hasSum R ratioSum hratio
  have hv := prime_filtered_tendsto_of_hasSum V varianceSum hvariance
  have hprod : Tendsto
      (fun s : Finset ℕ => ∑' m : Nat.factoredNumbers s,
        h (m : ℕ) * Real.log (m : ℝ)^2)
      atTop (𝓝 (mass * (ratioSum^2 + varianceSum))) := by
    apply (hm.mul ((hr.pow 2).add hv)).congr
    intro s
    exact (factored_second_logarithmic_moment_product h hmul M R V
      hlocal hlocalLog hlocalLogSq hnorm hlognorm hlogSqnorm s).tsum_eq.symm
  have hvalue : (∑' n : ℕ, h n * Real.log (n : ℝ)^2) =
      mass * (ratioSum^2 + varianceSum) :=
    tendsto_nhds_unique
      (factored_tsum_tendsto (fun n => h n * Real.log (n : ℝ)^2)
        hlogSqnorm.of_norm (by simp)) hprod
  exact hvalue ▸ hlogSqnorm.of_norm.hasSum

/-- An explicit summable envelope for the source's prime D-term. This bound
is only used to establish convergence, not as a numerical estimate for D. -/
theorem cubicSecondPrimeTerm_bounds (p : ℕ) (hp : 2 ≤ p) :
    0 ≤ cubicSecondPrimeTerm p ∧
      cubicSecondPrimeTerm p ≤ 512 * (p : ℝ)^(-(3/2 : ℝ)) := by
  let x : ℝ := p
  have hx2 : (2 : ℝ) ≤ x := by
    change (2 : ℝ) ≤ (p : ℝ)
    exact_mod_cast hp
  have hx : 0 < x := by linarith
  have hx1 : 0 < x-1 := by linarith
  have hn : 0 ≤ 8*x^2-10*x+4 := by
    nlinarith [mul_nonneg hx.le (show 0 ≤ 8*x-10 by linarith)]
  have hden : 0 < x^2*(x-1)^2 := mul_pos (sq_pos_of_pos hx) (sq_pos_of_pos hx1)
  have hratio : (8*x^2-10*x+4)/(x^2*(x-1)^2) ≤ 32/x^2 := by
    have hnum : 8*x^2-10*x+4 ≤ 32*(x-1)^2 := by
      nlinarith [sq_nonneg (x-2)]
    apply (div_le_div_iff₀ hden (sq_pos_of_pos hx)).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hnum (sq_nonneg x)]
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog : Real.log x ≤ x^(1/4 : ℝ)/(1/4 : ℝ) :=
    Real.log_natCast_le_rpow_div p (by norm_num : (0 : ℝ) < 1/4)
  have hlogSq := pow_le_pow_left₀ hlog0 hlog 2
  have hpow : (x^(1/4 : ℝ)/(1/4 : ℝ))^2 = 16*x^(1/2 : ℝ) := by
    calc
      _ = 16*(x^(1/4 : ℝ))^2 := by ring
      _ = 16*x^((1/4 : ℝ)*(2 : ℕ)) := by rw [Real.rpow_mul_natCast hx.le]
      _ = _ := by norm_num
  rw [hpow] at hlogSq
  have hpowers : x^(1/2 : ℝ)/x^2 = x^(-(3/2 : ℝ)) := by
    rw [← Real.rpow_sub_natCast hx.ne' (1/2 : ℝ) 2]
    norm_num
  change 0 ≤ (8*x^2-10*x+4)/(x^2*(x-1)^2)*Real.log x^2 ∧
    (8*x^2-10*x+4)/(x^2*(x-1)^2)*Real.log x^2 ≤ 512*x^(-(3/2 : ℝ))
  refine ⟨mul_nonneg (div_nonneg hn hden.le) (sq_nonneg _), ?_⟩
  calc
    _ ≤ (32/x^2)*Real.log x^2 :=
      mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
    _ ≤ (32/x^2)*(16*x^(1/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogSq (by positivity)
    _ = 512*(x^(1/2 : ℝ)/x^2) := by ring
    _ = _ := by rw [hpowers]

/-- Actual convergence of the all-prime second logarithmic series. -/
theorem summable_cubicSecondPrimeTerm :
    Summable (fun p : Nat.Primes => cubicSecondPrimeTerm (p : ℕ)) := by
  have hnat : Summable (fun n : ℕ => (512 : ℝ)*(n : ℝ)^(-(3/2 : ℝ))) :=
    (Real.summable_nat_rpow.mpr (by norm_num : -(3/2 : ℝ) < -1)).mul_left 512
  have hprime : Summable (fun p : Nat.Primes => (512 : ℝ)*(p : ℝ)^(-(3/2 : ℝ))) :=
    hnat.comp_injective Subtype.val_injective
  exact Summable.of_nonneg_of_le
    (fun p => (cubicSecondPrimeTerm_bounds p.val p.property.two_le).1)
    (fun p => (cubicSecondPrimeTerm_bounds p.val p.property.two_le).2) hprime

/-- Exact variance sum, including the positive quarter-log-two correction. -/
theorem cubic_log_variance_hasSum (D : ℝ)
    (hD : HasSum (fun p : Nat.Primes => cubicSecondPrimeTerm (p : ℕ)) D) :
    HasSum (fun p : Nat.Primes => cubicEulerLogVariance (p : ℕ))
      ((1/4 : ℝ)*Real.log 2^2-D) := by
  classical
  change HasSum
    (cubicSecondPrimeTerm ∘ Subtype.val (p := (· ∈ {p | Nat.Prime p}))) D at hD
  rw [hasSum_subtype_iff_indicator] at hD
  have hdelta : HasSum
      (fun p : ℕ => if p = 2 then (1/4 : ℝ)*Real.log 2^2 else 0)
      ((1/4 : ℝ)*Real.log 2^2) := hasSum_ite_eq 2 _
  have hr := hdelta.sub hD
  change HasSum
    (cubicEulerLogVariance ∘ Subtype.val (p := (· ∈ {p | Nat.Prime p}))) _
  rw [hasSum_subtype_iff_indicator]
  apply hr.congr_fun
  intro p
  by_cases hp : p.Prime
  · simp [Set.indicator, hp, cubicEulerLogVariance_eq_correction_sub]
  · have hp2 : p ≠ 2 := by
      intro he
      subst p
      exact hp Nat.prime_two
    simp [Set.indicator, hp, hp2]

/-- The actual signed second logarithmic moment of the same cubic correction.
All coefficient and prime-series convergence is derived from the explicit
prime-power data. The expression uses the actual public constant C. -/
theorem cubic_second_logarithmic_moment_hasSum
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    HasSum (fun n : ℕ => h n * Real.log (n : ℝ)^2)
      (((2 * (∑' p : Nat.Primes,
          Real.log (p : ℝ)/((p : ℝ)*((p : ℝ)-1))) + Real.log 2/2)^2 +
        (1/4 : ℝ)*Real.log 2^2 -
        (∑' p : Nat.Primes, cubicSecondPrimeTerm (p : ℕ))) /
          TaoFivePrimes.twinPrimeConstant) := by
  have hw := weighted_summable_of_cubic_prime_power_values h hmul hpv hpz
  have hn : Summable (fun n : ℕ => ‖h n‖) := by
    simpa only [pow_zero, mul_one] using
      logPower_norm_summable_of_weighted_summable h (2/5) (by norm_num) hw 0
  have hl : Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)‖) := by
    simpa only [pow_one] using
      logPower_norm_summable_of_weighted_summable h (2/5) (by norm_num) hw 1
  have hl2 := logPower_norm_summable_of_weighted_summable h (2/5) (by norm_num) hw 2
  have hm := hasSum_reciprocal_twinPrimeConstant_of_cubic_prime_power_values
    h hmul hpv hpz
  have hr := cubic_log_ratio_hasSum _ summable_prime_log_quotient.hasSum
  have hv := cubic_log_variance_hasSum _ summable_cubicSecondPrimeTerm.hasSum
  have hfull := hasSum_second_logarithmic_moment_of_local_euler
    h hmul cubicEulerMass cubicEulerLogRatio cubicEulerLogVariance _ _ _
    (fun p hp => cubic_local_mass h hmul p hp (hpv p hp) (fun k hk => hpz p k hp hk))
    (fun p hp => cubic_local_log_mass h p hp (hpv p hp) (fun k hk => hpz p k hp hk))
    (fun p hp => cubic_local_log_squared_mass h p hp (hpv p hp)
      (fun k hk => hpz p k hp hk))
    hn hl hl2 hm hr hv
  convert hfull using 1 <;> ring

end PrimePairConvolution





open scoped BigOperators

theorem solution
    (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    Summable (fun n : ℕ => ‖h n * Real.log (n : ℝ)^2‖) ∧
      HasSum (fun n : ℕ => h n * Real.log (n : ℝ)^2)
        (((2 * (∑' p : Nat.Primes,
            Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2 / 2)^2 +
          (1 / 4 : ℝ) * Real.log 2^2 -
          (∑' p : Nat.Primes,
            (8 * (p : ℝ)^2 - 10 * (p : ℝ) + 4) /
              ((p : ℝ)^2 * ((p : ℝ) - 1)^2) * Real.log (p : ℝ)^2)) /
            TaoFivePrimes.twinPrimeConstant) := by
  have hw := PrimePairConvolution.weighted_summable_of_cubic_prime_power_values
    h hmul hpv hpz
  refine ⟨PrimePairConvolution.logPower_norm_summable_of_weighted_summable
    h (2/5) (by norm_num) hw 2, ?_⟩
  simpa only [PrimePairConvolution.cubicSecondPrimeTerm] using
    PrimePairConvolution.cubic_second_logarithmic_moment_hasSum h hmul hpv hpz

#print axioms solution
