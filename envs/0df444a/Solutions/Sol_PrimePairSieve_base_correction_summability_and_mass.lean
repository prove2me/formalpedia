-- Prove2me | solution 1 for PrimePairSieve.base_correction_summability_and_mass
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T23:42:59.062119+00:00
-- url     : https://prove2.me/submissions/a57e4611-dcbc-45c2-8768-4ded05f5f6a4

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
This fragment is an uncompiled draft pending root's serial compiler queue.
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


/-- Convergence and reciprocal mass for one and the same correction. -/
theorem solution (h : ArithmeticFunction ℝ) (hmul : h.IsMultiplicative)
    (hpv : ∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2)
    (hpz : ∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) :
    Summable (fun n : ℕ => |h n| * (n : ℝ) ^ (2 / 5 : ℝ)) ∧
      HasSum (fun n : ℕ => h n) (1 / TaoFivePrimes.twinPrimeConstant) := by
  exact ⟨PrimePairConvolution.weighted_summable_of_cubic_prime_power_values h hmul hpv hpz,
    PrimePairConvolution.hasSum_reciprocal_twinPrimeConstant_of_cubic_prime_power_values
      h hmul hpv hpz⟩

#print axioms solution
