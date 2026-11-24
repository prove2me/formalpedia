-- Prove2me | solution 1 for PrimePairSieve.base_denominator_quadratic_expansion
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T00:27:04.093733+00:00
-- url     : https://prove2.me/submissions/146c3020-6ec4-45b7-8a29-977375dae034

import Definitions.Def_TaoFivePrimes_SingularSeries
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
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
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Data.Nat.Sqrt
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Group.InfiniteSum


set_option autoImplicit false
open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius

/-!
Finite algebra for the actual base-shift Selberg coefficients. The prime-local
weight is exactly the one in FiniteKernelComparison.lean: 1 at 2 and 2/(p-2)
at odd primes. This is not TaoFivePrimes.pairSieveWeight (which is different).

The division-by-n and Mobius prime-power proofs are adapted from the checked
RamareAnalytic.ConvolutionIdentity development. The second deconvolution and
the resulting cubic local factor are derived here. No analytic convergence,
constant estimate, or prime-pair bound is assumed or concluded.

Source: H. Riesel and R. C. Vaughan, On sums of primes (1983), equations
(2.5)–(2.6), printed p.46 (cubic correction), and (3.5), printed p.50
(double-harmonic convolution). See sources/riesel_vaughan_1983.pdf.
Root verifies this source against the pinned platform environment.
-/

namespace PrimePairConvolution

noncomputable def baseLocal (p : ℕ) : ℝ :=
  if p = 2 then 1 else 2 / ((p : ℝ) - 2)

noncomputable def baseCoefficient : ArithmeticFunction ℝ :=
  ⟨fun n => if Squarefree n then ∏ p ∈ n.primeFactors, baseLocal p else 0, by simp⟩

@[simp] theorem baseCoefficient_apply (n : ℕ) :
    baseCoefficient n =
      if Squarefree n then ∏ p ∈ n.primeFactors, baseLocal p else 0 := rfl

@[simp] theorem baseCoefficient_one : baseCoefficient 1 = 1 := by simp

@[simp] theorem baseCoefficient_prime (p : ℕ) (hp : p.Prime) :
    baseCoefficient p = baseLocal p := by simp [hp.squarefree, hp.primeFactors]

theorem baseCoefficient_prime_power_zero (p k : ℕ) (hp : p.Prime)
    (hk : 2 ≤ k) : baseCoefficient (p ^ k) = 0 := by
  have hn : ¬ Squarefree (p ^ k) := by
    rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
    simp [show k ≠ 1 by omega]
  simp [hn]

private noncomputable def divideByNat (f : ArithmeticFunction ℝ) :
    ArithmeticFunction ℝ := f.pdiv (ArithmeticFunction.id : ArithmeticFunction ℝ)

private theorem divideByNat_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    divideByNat f n = f n / (n : ℝ) := by simp [divideByNat]

private theorem divideByNat_mul (f g : ArithmeticFunction ℝ) :
    divideByNat (f * g) = divideByNat f * divideByNat g := by
  ext n
  simp only [divideByNat_apply, ArithmeticFunction.mul_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ab hab
  have he : (ab.1 : ℝ) * (ab.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hab).1
  rw [← he, div_mul_div_comm]

private noncomputable def weightedBase : ArithmeticFunction ℝ :=
  (ArithmeticFunction.id : ArithmeticFunction ℝ).pmul baseCoefficient

private theorem weightedBase_apply (n : ℕ) :
    weightedBase n = (n : ℝ) * baseCoefficient n := by simp [weightedBase]

private theorem weightedBase_one : weightedBase 1 = 1 := by simp [weightedBase_apply]

private theorem weightedBase_prime (p : ℕ) (hp : p.Prime) :
    weightedBase p = (p : ℝ) * baseLocal p := by
  rw [weightedBase_apply, baseCoefficient_prime p hp]

private theorem weightedBase_prime_power_zero (p k : ℕ) (hp : p.Prime)
    (hk : 2 ≤ k) : weightedBase (p ^ k) = 0 := by
  simp [weightedBase_apply, baseCoefficient_prime_power_zero p k hp hk]

noncomputable def harmonicKernel : ArithmeticFunction ℝ :=
  divideByNat (ζ : ArithmeticFunction ℝ)

@[simp] theorem harmonicKernel_apply (n : ℕ) :
    harmonicKernel n = 1 / (n : ℝ) := by
  by_cases hn : n = 0 <;> simp [harmonicKernel, divideByNat_apply, hn]

private noncomputable def firstDifference : ArithmeticFunction ℝ :=
  weightedBase * (μ : ArithmeticFunction ℝ)

/-- Explicit second Mobius deconvolution, with no assumed coefficient laws. -/
noncomputable def correction : ArithmeticFunction ℝ :=
  divideByNat (firstDifference * (μ : ArithmeticFunction ℝ))

theorem correction_convolution :
    (correction * harmonicKernel) * harmonicKernel = baseCoefficient := by
  unfold correction firstDifference harmonicKernel
  rw [← divideByNat_mul, ← divideByNat_mul]
  have hc :
      (((weightedBase * (μ : ArithmeticFunction ℝ)) * μ) * ζ) * ζ = weightedBase := by
    calc
      _ = weightedBase * (((μ : ArithmeticFunction ℝ) * ζ) * (μ * ζ)) := by ac_rfl
      _ = weightedBase := by
        simp only [ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
  rw [hc]
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [divideByNat_apply, weightedBase_apply]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)

private theorem Ioc_zero_eq_Icc_one (N : ℕ) :
    Finset.Ioc 0 N = Finset.Icc 1 N := by
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

private theorem harmonicKernel_sum (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, harmonicKernel n) = (harmonic N : ℝ) := by
  rw [Ioc_zero_eq_Icc_one, harmonic_eq_sum_Icc]
  simp [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

/-- Exact cumulative convolution of two harmonic kernels, including cutoff 0. -/
noncomputable def doubleHarmonic (N : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 N, (harmonic (N / a) : ℝ) / (a : ℝ)

private theorem doubleHarmonic_sum (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, (harmonicKernel * harmonicKernel) n) =
      doubleHarmonic N := by
  rw [ArithmeticFunction.sum_Ioc_mul_eq_sum_sum]
  simp_rw [harmonicKernel_sum]
  rw [Ioc_zero_eq_Icc_one]
  unfold doubleHarmonic
  apply Finset.sum_congr rfl
  intro a ha
  rw [harmonicKernel_apply]
  ring

/-- The actual sharp-cutoff base Selberg denominator is a finite double-harmonic
convolution. There are no convergence or asymptotic hypotheses. -/
theorem base_sum_eq_correction_doubleHarmonic (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then ∏ p ∈ n.primeFactors, baseLocal p else 0) =
      ∑ d ∈ Finset.Icc 1 N, correction d * doubleHarmonic (N / d) := by
  have hs := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum correction
    (harmonicKernel * harmonicKernel) N
  rw [← mul_assoc, correction_convolution] at hs
  simp_rw [doubleHarmonic_sum] at hs
  simpa only [Ioc_zero_eq_Icc_one, baseCoefficient_apply] using hs

private theorem mul_moebius_prime_power (f : ArithmeticFunction ℝ) (p k : ℕ)
    (hp : p.Prime) :
    (f * (μ : ArithmeticFunction ℝ)) (p ^ (k + 1)) =
      f (p ^ (k + 1)) - f (p ^ k) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (fun a b => f a * (μ : ArithmeticFunction ℝ) b),
    Nat.sum_divisors_prime_pow hp]
  change (∑ i ∈ Finset.range (k + 2),
    f (p ^ (k + 1) / p ^ i) * ((μ (p ^ i) : ℤ) : ℝ)) =
      f (p ^ (k + 1)) - f (p ^ k)
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ i ∈ Finset.range k,
      f (p ^ (k + 1) / p ^ (i + 1 + 1)) *
        ((μ (p ^ (i + 1 + 1)) : ℤ) : ℝ) = 0 := by
    intro i hi
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    simp [show i + 1 + 1 ≠ 1 by omega]
  rw [Finset.sum_eq_zero hz]
  simp only [pow_zero, pow_one, Nat.div_one, ArithmeticFunction.moebius_apply_one,
    ArithmeticFunction.moebius_apply_prime hp, Int.cast_one, Int.cast_neg,
    zero_add, mul_one, mul_neg_one]
  rw [Nat.pow_succ, Nat.mul_div_cancel _ hp.pos]
  ring

private theorem firstDifference_one : firstDifference 1 = 1 := by
  simp [firstDifference, ArithmeticFunction.mul_apply_one, weightedBase_one]

private theorem firstDifference_prime (p : ℕ) (hp : p.Prime) :
    firstDifference p = (p : ℝ) * baseLocal p - 1 := by
  simpa [firstDifference, weightedBase_prime p hp, weightedBase_one] using
    mul_moebius_prime_power weightedBase p 0 hp

private theorem firstDifference_prime_sq (p : ℕ) (hp : p.Prime) :
    firstDifference (p ^ 2) = -((p : ℝ) * baseLocal p) := by
  simpa [firstDifference, weightedBase_prime p hp,
    weightedBase_prime_power_zero p 2 hp (by omega)] using
    mul_moebius_prime_power weightedBase p 1 hp

private theorem firstDifference_prime_power_zero (p k : ℕ) (hp : p.Prime)
    (hk : 3 ≤ k) : firstDifference (p ^ k) = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    unfold firstDifference
    rw [mul_moebius_prime_power weightedBase p k hp,
      weightedBase_prime_power_zero p (k + 1) hp (by omega),
      weightedBase_prime_power_zero p k hp (by omega)]
    simp

@[simp] theorem correction_one : correction 1 = 1 := by
  simp [correction, divideByNat_apply, ArithmeticFunction.mul_apply_one,
    firstDifference_one]

theorem correction_prime (p : ℕ) (hp : p.Prime) :
    correction p = baseLocal p - 2 / (p : ℝ) := by
  have hm := mul_moebius_prime_power firstDifference p 0 hp
  simp only [Nat.zero_add, pow_one, pow_zero, firstDifference_prime p hp,
    firstDifference_one] at hm
  rw [correction, divideByNat_apply, hm]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [hp0] <;> ring

theorem correction_prime_sq (p : ℕ) (hp : p.Prime) :
    correction (p ^ 2) = 1 / (p : ℝ)^2 - 2 * baseLocal p / (p : ℝ) := by
  have hm := mul_moebius_prime_power firstDifference p 1 hp
  norm_num only [pow_one] at hm
  rw [firstDifference_prime_sq p hp, firstDifference_prime p hp] at hm
  rw [correction, divideByNat_apply, hm, Nat.cast_pow]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [hp0] <;> ring

theorem correction_prime_cube (p : ℕ) (hp : p.Prime) :
    correction (p ^ 3) = baseLocal p / (p : ℝ)^2 := by
  have hm := mul_moebius_prime_power firstDifference p 2 hp
  norm_num only at hm
  rw [firstDifference_prime_power_zero p 3 hp (by omega),
    firstDifference_prime_sq p hp] at hm
  rw [correction, divideByNat_apply, hm, Nat.cast_pow]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [hp0] <;> ring

theorem correction_prime_power_zero (p k : ℕ) (hp : p.Prime)
    (hk : 4 ≤ k) : correction (p ^ k) = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    rw [correction, divideByNat_apply, mul_moebius_prime_power firstDifference p k hp,
      firstDifference_prime_power_zero p (k + 1) hp (by omega),
      firstDifference_prime_power_zero p k hp (by omega)]
    simp

/-- The complete finite local Euler factor of the actual correction. -/
theorem correction_local_polynomial (p : ℕ) (hp : p.Prime) (t : ℝ) :
    1 + correction p * t + correction (p ^ 2) * t^2 +
      correction (p ^ 3) * t^3 =
      (1 + baseLocal p * t) * (1 - t / (p : ℝ))^2 := by
  rw [correction_prime p hp, correction_prime_sq p hp, correction_prime_cube p hp]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp [hp0] <;> ring

end PrimePairConvolution


/-! Append after BaseConvolution.lean in the same module: its private
weightedBase/firstDifference/divideByNat declarations are reused literally.
No analytic claim. This fragment has not been compiled by its author. -/

namespace PrimePairConvolution

theorem baseCoefficient_isMultiplicative : baseCoefficient.IsMultiplicative := by
  refine ⟨baseCoefficient_one, ?_⟩
  intro m n hcop
  by_cases hm : Squarefree m
  · by_cases hn : Squarefree n
    · simp only [baseCoefficient_apply, Nat.squarefree_mul hcop, hm, hn,
        and_self, if_true]
      have hm0 : m ≠ 0 := hm.ne_zero
      have hn0 : n ≠ 0 := hn.ne_zero
      have hmn0 : m * n ≠ 0 := mul_ne_zero hm0 hn0
      have hf := (ArithmeticFunction.IsMultiplicative.prodPrimeFactors baseLocal).2 hcop
      simpa only [ArithmeticFunction.prodPrimeFactors_apply hmn0,
        ArithmeticFunction.prodPrimeFactors_apply hm0,
        ArithmeticFunction.prodPrimeFactors_apply hn0] using hf
    · simp [baseCoefficient_apply, Nat.squarefree_mul hcop, hm, hn]
  · simp [baseCoefficient_apply, Nat.squarefree_mul hcop, hm]

theorem correction_isMultiplicative : correction.IsMultiplicative := by
  have hweighted : weightedBase.IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_id.natCast.pmul baseCoefficient_isMultiplicative
  have hmu : (μ : ArithmeticFunction ℝ).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_moebius.intCast
  exact ((hweighted.mul hmu).mul hmu).pdiv
    ArithmeticFunction.isMultiplicative_id.natCast

end PrimePairConvolution






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
Draft: a discrete Chebyshev estimate for the logarithmic prime moment in
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





set_option autoImplicit false
open scoped BigOperators

/-!
Exact finite hyperbola splitting and a finite-centred error estimate.
The identity is the opening step of Riesel--Vaughan (1983), Lemma 1,
printed p.48. This file does not claim their 1.641 x^(-1/3) remainder.
No correction coefficient, convergence, or Stieltjes constant is assumed.

The definition doubleHarmonic below is identical to BaseConvolution.lean.
A combined source must retain exactly one copy of that declaration.
Draft only: no compiler was invoked by the author of this file.
-/

namespace PrimePairConvolution


private theorem sum_Icc_ite_le (N m : ℕ) (hm : m ≤ N) (f : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc 1 N, if a ≤ m then f a else 0) =
      ∑ a ∈ Finset.Icc 1 m, f a := by
  rw [← Finset.sum_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

private theorem sum_Icc_mul_cut (N a : ℕ) (ha : 0 < a) (f : ℕ → ℝ) :
    (∑ b ∈ Finset.Icc 1 N, if a * b ≤ N then f a * f b else 0) =
      f a * ∑ b ∈ Finset.Icc 1 (N / a), f b := by
  rw [← Finset.sum_filter]
  have hs : (Finset.Icc 1 N).filter (fun b => a * b ≤ N) =
      Finset.Icc 1 (N / a) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hb, _⟩, hab⟩
      exact ⟨hb, (Nat.le_div_iff_mul_le ha).mpr (by simpa [Nat.mul_comm] using hab)⟩
    · rintro ⟨hb, hab⟩
      exact ⟨⟨hb, hab.trans (Nat.div_le_self N a)⟩,
        by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hab⟩
  rw [hs, Finset.mul_sum]

/-- Finite Dirichlet hyperbola splitting for an arbitrary real weight.
No sign assumption is needed, and the zero cutoff is included. -/
theorem finite_hyperbola (f : ℕ → ℝ) (N m : ℕ) (hmN : m ≤ N)
    (hm : m * m ≤ N) (hnext : N < (m + 1) * (m + 1)) :
    (∑ a ∈ Finset.Icc 1 N, f a * ∑ b ∈ Finset.Icc 1 (N / a), f b) =
      2 * (∑ a ∈ Finset.Icc 1 m, f a * ∑ b ∈ Finset.Icc 1 (N / a), f b) -
        (∑ a ∈ Finset.Icc 1 m, f a) ^ 2 := by
  classical
  let K : ℕ → ℕ → ℝ := fun a b => if a * b ≤ N then f a * f b else 0
  have hsplit (a b : ℕ) :
      K a b = (if a ≤ m then K a b else 0) +
        (if b ≤ m then K a b else 0) -
        (if a ≤ m ∧ b ≤ m then f a * f b else 0) := by
    by_cases ha : a ≤ m <;> by_cases hb : b ≤ m
    · have hab : a * b ≤ N := (Nat.mul_le_mul ha hb).trans hm
      simp [K, ha, hb, hab]
    · simp [ha, hb]
    · simp [ha, hb]
    · have hab : ¬ a * b ≤ N := by
        have hma : m + 1 ≤ a := by omega
        have hmb : m + 1 ≤ b := by omega
        exact not_le.mpr (hnext.trans_le (Nat.mul_le_mul hma hmb))
      simp [K, ha, hb, hab]
  have hsum :
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N, K a b) =
        (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          if a ≤ m then K a b else 0) +
        (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          if b ≤ m then K a b else 0) -
        (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
          if a ≤ m ∧ b ≤ m then f a * f b else 0) := by
    simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun b _ => hsplit a b))
  have hleft :
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        if a ≤ m then K a b else 0) =
      ∑ a ∈ Finset.Icc 1 m, ∑ b ∈ Finset.Icc 1 N, K a b := by
    calc
      _ = ∑ a ∈ Finset.Icc 1 N,
          if a ≤ m then (∑ b ∈ Finset.Icc 1 N, K a b) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a ≤ m <;> simp [ha]
      _ = _ := sum_Icc_ite_le N m hmN _
  have hright :
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        if b ≤ m then K a b else 0) =
      ∑ a ∈ Finset.Icc 1 m, ∑ b ∈ Finset.Icc 1 N, K a b := by
    rw [Finset.sum_comm]
    convert hleft using 1
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp only [K, Nat.mul_comm, mul_comm]
  have hcorner :
      (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
        if a ≤ m ∧ b ≤ m then f a * f b else 0) =
      (∑ a ∈ Finset.Icc 1 m, f a) ^ 2 := by
    calc
      _ = ∑ a ∈ Finset.Icc 1 N,
          if a ≤ m then (∑ b ∈ Finset.Icc 1 m, f a * f b) else 0 := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : a ≤ m
        · simp only [ha, true_and, if_true]
          exact sum_Icc_ite_le N m hmN _
        · simp [ha]
      _ = ∑ a ∈ Finset.Icc 1 m, ∑ b ∈ Finset.Icc 1 m, f a * f b :=
        sum_Icc_ite_le N m hmN _
      _ = _ := by rw [← Finset.sum_mul_sum, pow_two]
  have hstrip (r : ℕ) :
      (∑ a ∈ Finset.Icc 1 r, ∑ b ∈ Finset.Icc 1 N, K a b) =
      ∑ a ∈ Finset.Icc 1 r, f a * ∑ b ∈ Finset.Icc 1 (N / a), f b := by
    apply Finset.sum_congr rfl
    intro a ha
    exact sum_Icc_mul_cut N a (Finset.mem_Icc.mp ha).1 f
  rw [hleft, hright, hcorner, hstrip N, hstrip m] at hsum
  linarith

private theorem harmonic_sum_real (N : ℕ) :
    (harmonic N : ℝ) = ∑ a ∈ Finset.Icc 1 N, (a : ℝ)⁻¹ := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

/-- The exact sqrt-cutoff identity for the literal BaseConvolution kernel. -/
theorem doubleHarmonic_hyperbola (N : ℕ) :
    doubleHarmonic N =
      2 * (∑ a ∈ Finset.Icc 1 (Nat.sqrt N),
        (harmonic (N / a) : ℝ) / (a : ℝ)) - (harmonic (Nat.sqrt N) : ℝ)^2 := by
  have h := finite_hyperbola (fun a => (a : ℝ)⁻¹) N (Nat.sqrt N)
    (Nat.sqrt_le_self N) (Nat.sqrt_le N) (Nat.lt_succ_sqrt N)
  simp only [← harmonic_sum_real] at h
  simpa only [doubleHarmonic, div_eq_mul_inv, mul_comm] using h

-- Adapted from the checked private harmonic_error_le_inverse in
-- discovery_ramare_large/HarmonicError.lean; no use of its public 2/5-power bound.
private theorem harmonic_interval_error (n : ℕ) (hn : 0 < n)
    (t : ℝ) (hnt : (n : ℝ) ≤ t) (htn : t < (n : ℝ) + 1) :
    |(harmonic n : ℝ) - Real.log t - Real.eulerMascheroniConstant| ≤
      1 / (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have ht : 0 < t := hnR.trans_le hnt
  have hglo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  change (harmonic n : ℝ) - Real.log ((n : ℝ) + 1) <
    Real.eulerMascheroniConstant at hglo
  have hghi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  simp only [Real.eulerMascheroniSeq', hn.ne', if_false] at hghi
  have hloglo := Real.log_le_log hnR hnt
  have hloghi := Real.log_le_log ht htn.le
  have hgap : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (div_pos (by positivity : 0 < (n : ℝ) + 1) hnR)
    rw [Real.log_div (by positivity) hnR.ne'] at h
    have heq : ((n : ℝ) + 1) / (n : ℝ) - 1 = 1 / (n : ℝ) := by
      field_simp [hnR.ne'] <;> ring
    rwa [heq] at h
  apply abs_le.mpr
  constructor <;> linarith

private theorem harmonic_quotient_error (N a : ℕ) (ha : 0 < a) (haN : a ≤ N) :
    |(harmonic (N / a) : ℝ) - Real.log ((N : ℝ) / a) -
      Real.eulerMascheroniConstant| ≤ 2 * (a : ℝ) / N := by
  have hN : 0 < N := ha.trans_le haN
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hNR : 0 < (N : ℝ) := by exact_mod_cast hN
  have ht : 1 ≤ (N : ℝ) / a := (le_div_iff₀ haR).mpr (by
    simpa only [one_mul] using (show (a : ℝ) ≤ (N : ℝ) by exact_mod_cast haN))
  have hfloor : ⌊(N : ℝ) / a⌋₊ = N / a := Nat.floor_div_eq_div N a
  have hk : 0 < N / a := by rw [← hfloor]; exact Nat.floor_pos.mpr ht
  have hnt : ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / a := by
    rw [← hfloor]
    exact Nat.floor_le (by positivity)
  have htn : (N : ℝ) / a < ((N / a : ℕ) : ℝ) + 1 := by
    rw [← hfloor]
    exact Nat.lt_floor_add_one _
  have hk1 : (1 : ℝ) ≤ ((N / a : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ N / a by omega)
  have hmajor : (N : ℝ) ≤ 2 * (a : ℝ) * ((N / a : ℕ) : ℝ) := by
    have hlt := (div_lt_iff₀ haR).mp htn
    calc
      _ ≤ (((N / a : ℕ) : ℝ) + 1) * a := hlt.le
      _ ≤ (2 * ((N / a : ℕ) : ℝ)) * a :=
        mul_le_mul_of_nonneg_right (by linarith) haR.le
      _ = _ := by ring
  have hi : 1 / ((N / a : ℕ) : ℝ) ≤ 2 * (a : ℝ) / N := by
    apply (div_le_div_iff₀ (by exact_mod_cast hk : (0 : ℝ) < ((N / a : ℕ) : ℝ)) hNR).mpr
    simpa only [one_mul] using hmajor
  exact (harmonic_interval_error (N / a) hk ((N : ℝ) / a) hnt htn).trans hi

/-- A finite-centred O(N^(-1/2)) error, without a Stieltjes-constant premise.
The centre still contains the explicit finite logarithmic sum at sqrt N. -/
theorem doubleHarmonic_finite_center_error (N : ℕ) (hN : 1 ≤ N) :
    |doubleHarmonic N -
      (2 * (Real.log (N : ℝ) + Real.eulerMascheroniConstant) *
        (harmonic (Nat.sqrt N) : ℝ) -
       2 * (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), Real.log (a : ℝ) / a) -
       (harmonic (Nat.sqrt N) : ℝ)^2)| ≤ 4 * (Nat.sqrt N : ℝ) / N := by
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  let E : ℕ → ℝ := fun a =>
    ((harmonic (N / a) : ℝ) - Real.log ((N : ℝ) / a) -
      Real.eulerMascheroniConstant) / a
  have hterm : ∀ a ∈ Finset.Icc 1 (Nat.sqrt N), |E a| ≤ 2 / (N : ℝ) := by
    intro a ha
    have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
    have haN : a ≤ N := (Finset.mem_Icc.mp ha).2.trans (Nat.sqrt_le_self N)
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha0
    dsimp only [E]
    rw [abs_div, abs_of_pos haR]
    calc
      _ ≤ (2 * (a : ℝ) / N) / a :=
        div_le_div_of_nonneg_right (harmonic_quotient_error N a ha0 haN) haR.le
      _ = 2 / (N : ℝ) := by field_simp [haR.ne', hNR.ne']
  have hsum : |∑ a ∈ Finset.Icc 1 (Nat.sqrt N), E a| ≤
      (Nat.sqrt N : ℝ) * (2 / (N : ℝ)) := by
    calc
      _ ≤ ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), |E a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), (2 / (N : ℝ)) :=
        Finset.sum_le_sum hterm
      _ = _ := by simp
  have hdecomp :
      (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), (harmonic (N / a) : ℝ) / a) =
      (Real.log (N : ℝ) + Real.eulerMascheroniConstant) *
        (harmonic (Nat.sqrt N) : ℝ) -
      (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), Real.log (a : ℝ) / a) +
      ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), E a := by
    conv_rhs =>
      rw [harmonic_sum_real, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have ha0 : 0 < a := (Finset.mem_Icc.mp ha).1
    have haR : 0 < (a : ℝ) := by exact_mod_cast ha0
    dsimp only [E]
    rw [Real.log_div hNR.ne' haR.ne']
    ring
  rw [doubleHarmonic_hyperbola, hdecomp]
  have heq :
      2 * ((Real.log (N : ℝ) + Real.eulerMascheroniConstant) *
        (harmonic (Nat.sqrt N) : ℝ) -
        (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), Real.log (a : ℝ) / a) +
        ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), E a) -
      (harmonic (Nat.sqrt N) : ℝ)^2 -
      (2 * (Real.log (N : ℝ) + Real.eulerMascheroniConstant) *
        (harmonic (Nat.sqrt N) : ℝ) -
        2 * (∑ a ∈ Finset.Icc 1 (Nat.sqrt N), Real.log (a : ℝ) / a) -
        (harmonic (Nat.sqrt N) : ℝ)^2) =
      2 * ∑ a ∈ Finset.Icc 1 (Nat.sqrt N), E a := by ring
  rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ 2 * ((Nat.sqrt N : ℝ) * (2 / (N : ℝ))) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = _ := by ring

end PrimePairConvolution




set_option autoImplicit false
open scoped BigOperators Topology
open Filter Set MeasureTheory

/-!
Construction of the first Stieltjes constant from finite log-weighted harmonic
sums, with an explicit elementary remainder. The convention is
gamma_1 = lim_n (sum_{a=1}^n log(a)/a - log(n)^2/2), as in Riesel--Vaughan
(1983), equation (2.1), printed p.45. No numerical value, asymptotic estimate,
Euler--Maclaurin formula, or sieve-coefficient hypothesis is assumed.

This is a standalone uncompiled draft; root owns all compiler runs.
-/

namespace PrimePairConvolution

noncomputable def logWeightedHarmonic (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, Real.log (i + 1 : ℕ) / (i + 1 : ℕ)

theorem logWeightedHarmonic_eq_sum_Icc (n : ℕ) :
    logWeightedHarmonic n =
      ∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / a := by
  rw [logWeightedHarmonic, Finset.range_eq_Ico,
    Finset.sum_Ico_add' (fun a : ℕ => Real.log (a : ℝ) / a) 0 n (c := 1)]
  simp only [Finset.Ico_add_one_right_eq_Icc]

private theorem logWeightedHarmonic_succ (n : ℕ) :
    logWeightedHarmonic (n + 1) = logWeightedHarmonic n +
      Real.log (n + 1 : ℕ) / (n + 1 : ℕ) := by
  simp only [logWeightedHarmonic, Finset.sum_range_succ]

noncomputable def firstStieltjesSeq (n : ℕ) : ℝ :=
  logWeightedHarmonic n - Real.log (n : ℝ)^2 / 2

private theorem log_div_self_antitone_three :
    AntitoneOn (fun x : ℝ => Real.log x / x) (Set.Ici 3) := by
  apply Real.log_div_self_antitoneOn.mono
  intro x hx
  exact Real.exp_one_lt_three.le.trans hx

private theorem integral_log_div_self {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) :
    (∫ x in a..b, Real.log x / x) =
      Real.log b ^ 2 / 2 - Real.log a ^ 2 / 2 := by
  have hx0 : ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    have : 3 ≤ x := ha.trans hx.1
    linarith
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun x : ℝ => Real.log x ^ 2 / 2)
  · intro x hx
    apply (((Real.hasDerivAt_log (hx0 x hx)).fun_pow 2).div_const 2).congr_deriv
    norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat]
    ring
  · apply AntitoneOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact log_div_self_antitone_three.mono (fun x hx => ha.trans hx.1)

/-- One-step errors lie between zero and an explicit telescoping difference. -/
theorem firstStieltjesSeq_step (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ firstStieltjesSeq n - firstStieltjesSeq (n + 1) ∧
    firstStieltjesSeq n - firstStieltjesSeq (n + 1) ≤
      Real.log (n : ℝ) / n - Real.log (n + 1 : ℕ) / (n + 1 : ℕ) := by
  have hnR : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hf : AntitoneOn (fun x : ℝ => Real.log x / x)
      (Set.Icc (n : ℝ) ((n : ℝ) + (1 : ℕ))) :=
    log_div_self_antitone_three.mono (fun x hx => hnR.trans hx.1)
  have hlo := hf.sum_le_integral (a := 1)
  have hup := hf.integral_le_sum (a := 1)
  have hi := integral_log_div_self hnR
    (show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
  norm_num only [Finset.sum_range_one, Nat.cast_zero, Nat.cast_one,
    Nat.zero_add, add_zero] at hlo hup
  rw [hi] at hlo hup
  simp only [firstStieltjesSeq, logWeightedHarmonic_succ, Nat.cast_add,
    Nat.cast_one]
  constructor <;> linarith

private theorem firstStieltjesSeq_shift_antitone :
    Antitone (fun n : ℕ => firstStieltjesSeq (n + 3)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := (firstStieltjesSeq_step (n + 3) (by omega)).1
  have he : n + 1 + 3 = n + 3 + 1 := by omega
  rw [he]
  linarith

private theorem firstStieltjesSeq_lower_shift_monotone :
    Monotone (fun n : ℕ => firstStieltjesSeq (n + 3) -
      Real.log (n + 3 : ℕ) / (n + 3 : ℕ)) := by
  apply monotone_nat_of_le_succ
  intro n
  have h := (firstStieltjesSeq_step (n + 3) (by omega)).2
  have he : n + 1 + 3 = n + 3 + 1 := by omega
  rw [he]
  linarith

private theorem firstStieltjesSeq_lower_le (n : ℕ) :
    firstStieltjesSeq (n + 3) - Real.log (n + 3 : ℕ) / (n + 3 : ℕ) ≤
      firstStieltjesSeq (n + 3) := by
  have hlog : 0 ≤ Real.log (n + 3 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 3 by omega))
  have hdiv : 0 ≤ Real.log (n + 3 : ℕ) / (n + 3 : ℕ) :=
    div_nonneg hlog (Nat.cast_nonneg _)
  linarith

private theorem firstStieltjesSeq_cross (n k : ℕ) :
    firstStieltjesSeq (n + 3) - Real.log (n + 3 : ℕ) / (n + 3 : ℕ) ≤
      firstStieltjesSeq (k + 3) := by
  exact (firstStieltjesSeq_lower_shift_monotone (le_max_left n k)).trans
    ((firstStieltjesSeq_lower_le (max n k)).trans
      (firstStieltjesSeq_shift_antitone (le_max_right n k)))

private theorem firstStieltjesSeq_bddBelow :
    BddBelow (Set.range (fun n : ℕ => firstStieltjesSeq (n + 3))) := by
  refine ⟨firstStieltjesSeq 3 - Real.log 3 / 3, ?_⟩
  rintro _ ⟨n, rfl⟩
  simpa only [Nat.zero_add, Nat.cast_ofNat] using firstStieltjesSeq_cross 0 n

/-- The first Stieltjes constant in the log-weighted-sum convention. -/
noncomputable def firstStieltjesConstant : ℝ :=
  ⨅ n : ℕ, firstStieltjesSeq (n + 3)

/-- Convergence is proved from the concrete elementary two-sequence enclosure. -/
theorem tendsto_firstStieltjesSeq :
    Tendsto firstStieltjesSeq atTop (𝓝 firstStieltjesConstant) := by
  apply (tendsto_add_atTop_iff_nat 3).mp
  exact tendsto_atTop_ciInf firstStieltjesSeq_shift_antitone firstStieltjesSeq_bddBelow

/-- Explicit one-sided remainder for all natural cutoffs at least three. -/
theorem firstStieltjesSeq_error (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ firstStieltjesSeq n - firstStieltjesConstant ∧
    firstStieltjesSeq n - firstStieltjesConstant ≤ Real.log (n : ℝ) / n := by
  have he : n - 3 + 3 = n := Nat.sub_add_cancel hn
  have hupper : firstStieltjesConstant ≤ firstStieltjesSeq n := by
    unfold firstStieltjesConstant
    simpa only [he] using ciInf_le firstStieltjesSeq_bddBelow (n - 3)
  have hlower : firstStieltjesSeq n - Real.log (n : ℝ) / n ≤
      firstStieltjesConstant := by
    unfold firstStieltjesConstant
    apply le_ciInf
    intro k
    simpa only [he] using firstStieltjesSeq_cross (n - 3) k
  constructor <;> linarith

/-- Literal finite-sum form used by the double-harmonic estimate. -/
theorem logWeightedHarmonic_error (n : ℕ) (hn : 3 ≤ n) :
    0 ≤ (∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / a) -
      Real.log (n : ℝ)^2 / 2 - firstStieltjesConstant ∧
    (∑ a ∈ Finset.Icc 1 n, Real.log (a : ℝ) / a) -
      Real.log (n : ℝ)^2 / 2 - firstStieltjesConstant ≤ Real.log (n : ℝ) / n := by
  simpa only [firstStieltjesSeq, logWeightedHarmonic_eq_sum_Icc] using
    firstStieltjesSeq_error n hn

end PrimePairConvolution



/-!
Assemble the checked finite hyperbola estimate with the constructed first
Stieltjes constant. This fragment follows DoubleHarmonic.lean and
LogWeightedHarmonic.lean in one module. It assumes no asymptotic estimate.
The centre is Riesel--Vaughan (1983), Lemma 1, printed p.48; the elementary
explicit remainder here is different from their sharper numerical bound.
-/

namespace PrimePairConvolution

/-- An explicit error for the actual double-harmonic kernel, with the constant
constructed as the limit of the logarithmically weighted harmonic sums. -/
theorem doubleHarmonic_asymptotic_error (N : ℕ) (hN : 9 ≤ N) :
    |doubleHarmonic N -
      (Real.log (N : ℝ)^2 / 2 +
        2 * Real.eulerMascheroniConstant * Real.log (N : ℝ) +
        Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant)| ≤
      3 / (Nat.sqrt N : ℝ)^2 + 2 * Real.log (N : ℝ) / Nat.sqrt N +
        4 * (Nat.sqrt N : ℝ) / N := by
  let m := Nat.sqrt N
  have hm3 : 3 ≤ m := Nat.le_sqrt.mpr hN
  have hm0 : 0 < m := by omega
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm0
  have hNR : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hmN : (m : ℝ)^2 ≤ (N : ℝ) := by
    exact_mod_cast Nat.sqrt_le' N
  have hNm : (N : ℝ) < ((m : ℝ) + 1)^2 := by
    exact_mod_cast Nat.lt_succ_sqrt' N
  let L := Real.log (N : ℝ)
  let l := Real.log (m : ℝ)
  let a := (m : ℝ)⁻¹
  let e := (harmonic m : ℝ) - l - Real.eulerMascheroniConstant
  let s := (∑ i ∈ Finset.Icc 1 m, Real.log (i : ℝ) / i) -
    l^2 / 2 - firstStieltjesConstant
  have ha0 : 0 ≤ a := inv_nonneg.mpr hmR.le
  have hl0 : 0 ≤ l := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ m by omega))
  have hL0 : 0 ≤ L := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ N by omega))
  have hloglower : 2 * l ≤ L := by
    have h := Real.log_le_log (sq_pos_of_pos hmR) hmN
    simpa only [Real.log_pow, Nat.cast_ofNat, L, l] using h
  have hlogupper : L ≤ 2 * Real.log ((m : ℝ) + 1) := by
    have h := Real.log_le_log hNR hNm.le
    simpa only [Real.log_pow, Nat.cast_ofNat, L] using h
  have hgap : Real.log ((m : ℝ) + 1) - l ≤ a := by
    have h := Real.log_le_sub_one_of_pos
      (div_pos (by positivity : 0 < (m : ℝ) + 1) hmR)
    rw [Real.log_div (by positivity) hmR.ne'] at h
    have heq : ((m : ℝ) + 1) / m - 1 = a := by
      dsimp [a]
      field_simp [hmR.ne'] <;> ring
    simpa only [l, heq] using h
  have hu : (l - L / 2)^2 ≤ a^2 := by
    have hlo : 0 ≤ L / 2 - l := by linarith
    have hhi : L / 2 - l ≤ a := by linarith
    nlinarith [mul_nonneg hlo (by linarith : 0 ≤ a - (L / 2 - l))]
  have he0 : 0 ≤ e := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' m
    simp only [Real.eulerMascheroniSeq', hm0.ne', if_false] at h
    dsimp [e, l]
    linarith
  have hea : e ≤ a := by
    have h := (abs_le.mp (harmonic_interval_error m hm0 (m : ℝ)
      le_rfl (by linarith))).2
    simpa only [e, l, a, one_div] using h
  have he2 : e^2 ≤ a^2 := by
    nlinarith [mul_nonneg he0 (sub_nonneg.mpr hea)]
  have hs := logWeightedHarmonic_error m hm3
  change 0 ≤ s ∧ s ≤ l / (m : ℝ) at hs
  have hsa : s ≤ l * a := by simpa only [div_eq_mul_inv, a] using hs.2
  have hLl : 0 ≤ L - l := by linarith
  have hcross : 2 * (L - l) * e ≤ 2 * (L - l) * a :=
    mul_le_mul_of_nonneg_left hea (by positivity)
  have hcross0 : 0 ≤ 2 * (L - l) * e := by positivity
  have hLa : l * a ≤ L * a := mul_le_mul_of_nonneg_right (by linarith) ha0
  have hcenter :
      |(2 * (L + Real.eulerMascheroniConstant) * (harmonic m : ℝ) -
          2 * (∑ i ∈ Finset.Icc 1 m, Real.log (i : ℝ) / i) -
          (harmonic m : ℝ)^2) -
        (L^2 / 2 + 2 * Real.eulerMascheroniConstant * L +
          Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant)| ≤
      3 * a^2 + 2 * L * a := by
    have heq :
        (2 * (L + Real.eulerMascheroniConstant) * (harmonic m : ℝ) -
            2 * (∑ i ∈ Finset.Icc 1 m, Real.log (i : ℝ) / i) -
            (harmonic m : ℝ)^2) -
          (L^2 / 2 + 2 * Real.eulerMascheroniConstant * L +
            Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant) =
        -2 * (l - L / 2)^2 + 2 * (L - l) * e - e^2 - 2 * s := by
      dsimp [e, s]
      ring
    rw [heq]
    apply abs_le.mpr
    constructor
    · nlinarith [sq_nonneg e, sq_nonneg (l - L / 2)]
    · have hla0 : 0 ≤ l * a := mul_nonneg hl0 ha0
      nlinarith [sq_nonneg e, sq_nonneg (l - L / 2), sq_nonneg a]
  have hfinite := doubleHarmonic_finite_center_error N (by omega)
  have htri := (abs_sub_le (doubleHarmonic N)
    (2 * (L + Real.eulerMascheroniConstant) * (harmonic m : ℝ) -
      2 * (∑ i ∈ Finset.Icc 1 m, Real.log (i : ℝ) / i) -
      (harmonic m : ℝ)^2)
    (L^2 / 2 + 2 * Real.eulerMascheroniConstant * L +
      Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant)).trans
    (add_le_add hfinite hcenter)
  simpa only [L, a, m, div_eq_mul_inv, inv_pow,
    add_comm, add_left_comm, add_assoc] using htri

end PrimePairConvolution


/-!
Append to the checked DoubleKernelEstimate.lean, adding
Mathlib.Analysis.SpecialFunctions.Pow.Real to its imports.
An explicit coarse remainder for every positive real cutoff, including the
empty-sum regime. The constant below is not the sharper source constant 1.641.
Draft: not yet compiled. No coefficient or sieve estimate is assumed.
-/

namespace PrimePairConvolution

private noncomputable def quadraticKernelCenter (g c t : ℝ) : ℝ :=
  Real.log t ^ 2 / 2 + 2 * g * Real.log t + g ^ 2 - 2 * c

private theorem quadraticKernelCenter_abs (g c t : ℝ) :
    |quadraticKernelCenter g c t| ≤
      Real.log t ^ 2 / 2 + 2 * |g| * |Real.log t| + g ^ 2 + 2 * |c| := by
  unfold quadraticKernelCenter
  calc
    _ ≤ |Real.log t ^ 2 / 2 + 2 * g * Real.log t + g ^ 2| + |-2 * c| := by
      convert abs_add_le (Real.log t ^ 2 / 2 + 2 * g * Real.log t + g ^ 2)
        (-2 * c) using 1 <;> congr 1 <;> ring
    _ ≤ ((|Real.log t ^ 2 / 2| + |2 * g * Real.log t|) + |g ^ 2|) +
        |-2 * c| := by
      linarith only [abs_add_le (Real.log t ^ 2 / 2 + 2 * g * Real.log t) (g ^ 2),
        abs_add_le (Real.log t ^ 2 / 2) (2 * g * Real.log t)]
    _ = _ := by simp only [abs_div, abs_pow, abs_mul]; norm_num

private theorem doubleHarmonic_nonneg_le_sq (N : ℕ) :
    0 ≤ doubleHarmonic N ∧ doubleHarmonic N ≤ (N : ℝ)^2 := by
  have hH (n : ℕ) : 0 ≤ (harmonic n : ℝ) ∧ (harmonic n : ℝ) ≤ (n : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    constructor
    · exact Finset.sum_nonneg (fun i hi => by positivity)
    · calc
        _ ≤ ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
          exact inv_le_one_of_one_le₀ hi1
        _ = _ := by simp
  constructor
  · exact Finset.sum_nonneg (fun a ha => div_nonneg (hH (N / a)).1 (by positivity))
  · calc
      _ ≤ ∑ a ∈ Finset.Icc 1 N, (N : ℝ) := by
        apply Finset.sum_le_sum
        intro a ha
        have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast (Finset.mem_Icc.mp ha).1
        have haq : 0 < (a : ℝ) := by linarith
        have hdiv : ((N / a : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self N a
        apply (div_le_iff₀ haq).mpr
        exact ((hH _).2.trans hdiv).trans
          (le_mul_of_one_le_right (by positivity) ha1)
      _ = _ := by simp [pow_two]

private theorem rpow_sixth_powers (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 / 6 : ℝ)) ^ 2 = x ^ (1 / 3 : ℝ) ∧
    (x ^ (1 / 6 : ℝ)) ^ 6 = x := by
  constructor
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num

private theorem integer_kernel_error_scaled (N : ℕ) (hN : 9 ≤ N) :
    |doubleHarmonic N - quadraticKernelCenter Real.eulerMascheroniConstant
        firstStieltjesConstant (N : ℝ)| * (N : ℝ) ^ (1 / 3 : ℝ) ≤ 40 := by
  let x : ℝ := N
  let m : ℝ := Nat.sqrt N
  let u : ℝ := x ^ (1 / 6 : ℝ)
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ N by omega)
  have hx0 : 0 < x := by linarith
  have hm1 : 1 ≤ m := by
    dsimp [m]
    exact_mod_cast (Nat.le_sqrt.mpr (show 1 * 1 ≤ N by omega))
  have hm0 : 0 < m := by linarith
  have hmx : m^2 ≤ x := by
    dsimp only [m, x]
    exact_mod_cast Nat.sqrt_le' N
  have hxm : x < (m + 1)^2 := by
    dsimp only [m, x]
    exact_mod_cast Nat.lt_succ_sqrt' N
  have hx4 : x ≤ 4 * m^2 := by nlinarith
  have hu1 : 1 ≤ u := Real.one_le_rpow hx1 (by norm_num)
  have hu0 : 0 ≤ u := by linarith
  have hu2 : u^2 = x ^ (1 / 3 : ℝ) := (rpow_sixth_powers x hx0.le).1
  have hu6 : u^6 = x := (rpow_sixth_powers x hx0.le).2
  have hu3sq : (u^3)^2 = x := by simpa only [← pow_mul] using hu6
  have hmlo : u^3 ≤ 2*m := (sq_le_sq₀ (by positivity) (by positivity)).mp (by
    rw [hu3sq]
    nlinarith)
  have hmhi : m ≤ u^3 := (sq_le_sq₀ hm0.le (by positivity)).mp (by
    rw [hu3sq]
    exact hmx)
  have hlog : Real.log x ≤ 6*u := by
    have h := Real.log_le_rpow_div hx0.le (by norm_num : (0 : ℝ) < 1/6)
    change Real.log x ≤ u / (1/6 : ℝ) at h
    linarith
  have hu2x : u^2 ≤ x := by
    rw [hu2]
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (1/3 : ℝ) ≤ 1)
  have hfirst : (3 / m^2) * u^2 ≤ 12 := by
    have hbound : 3 * u^2 ≤ 12 * m^2 := by nlinarith
    calc
      _ = (3 * u^2) / m^2 := by ring
      _ ≤ 12 := (div_le_iff₀ (sq_pos_of_pos hm0)).mpr hbound
  have hsecond : (2 * Real.log x / m) * u^2 ≤ 24 := by
    have hb := mul_le_mul_of_nonneg_right hlog (sq_nonneg u)
    have hc : 2 * Real.log x * u^2 ≤ 24*m := by nlinarith
    calc
      _ = (2 * Real.log x * u^2) / m := by ring
      _ ≤ 24 := (div_le_iff₀ hm0).mpr hc
  have hthird : (4*m/x)*u^2 ≤ 4 := by
    have hb := mul_le_mul_of_nonneg_right hmhi (sq_nonneg u)
    have hc : u^5 ≤ u^6 := pow_le_pow_right₀ hu1 (by decide)
    have hd : m * u^2 ≤ x := by nlinarith
    calc
      _ = (4*m*u^2)/x := by ring
      _ ≤ 4 := (div_le_iff₀ hx0).mpr (by nlinarith)
  have he := mul_le_mul_of_nonneg_right
    (doubleHarmonic_asymptotic_error N hN) (sq_nonneg u)
  change |doubleHarmonic N - quadraticKernelCenter Real.eulerMascheroniConstant
    firstStieltjesConstant x| * u^2 ≤
    (3 / m^2 + 2 * Real.log x / m + 4*m/x) * u^2 at he
  rw [← hu2]
  nlinarith

private theorem center_floor_shift_scaled (g c t : ℝ) (ht : 1 ≤ t) :
    |quadraticKernelCenter g c (⌊t⌋₊ : ℝ) - quadraticKernelCenter g c t| *
      t ^ (1 / 3 : ℝ) ≤ 6 + 4 * |g| := by
  let n : ℝ := ⌊t⌋₊
  let L := Real.log t
  let l := Real.log n
  let w := t ^ (1 / 3 : ℝ)
  have ht0 : 0 < t := by linarith
  have hn1 : 1 ≤ n := by
    have hn : 1 ≤ ⌊t⌋₊ := Nat.floor_pos.mpr ht
    dsimp only [n]
    exact_mod_cast hn
  have hn0 : 0 < n := by linarith
  have hnt : n ≤ t := Nat.floor_le ht0.le
  have htn : t < n + 1 := Nat.lt_floor_add_one t
  have ht2n : t ≤ 2*n := by linarith
  have hl0 : 0 ≤ l := Real.log_nonneg hn1
  have hL0 : 0 ≤ L := Real.log_nonneg ht
  have hlL : l ≤ L := Real.log_le_log hn0 hnt
  have hgap : L-l ≤ 1/n := by
    have h := Real.log_le_sub_one_of_pos (div_pos ht0 hn0)
    rw [Real.log_div ht0.ne' hn0.ne'] at h
    have hdiv : t/n ≤ (n+1)/n := div_le_div_of_nonneg_right htn.le hn0.le
    have heq : (n+1)/n-1 = 1/n := by field_simp [hn0.ne']; ring
    have hd : t/n-1 ≤ 1/n := by linarith
    dsimp [L, l]
    linarith
  have hpoly : |quadraticKernelCenter g c n - quadraticKernelCenter g c t| ≤
      (L + 2* |g|)/n := by
    have hid : quadraticKernelCenter g c n - quadraticKernelCenter g c t =
        -(L-l) * ((L+l)/2+2*g) := by dsimp [quadraticKernelCenter, L, l]; ring
    have hab : |(L+l)/2+2*g| ≤ L+2* |g| := by
      calc
        _ ≤ |(L+l)/2|+|2*g| := abs_add_le _ _
        _ ≤ L+2* |g| := by
          rw [abs_of_nonneg (by positivity), abs_mul]
          norm_num
          linarith
    rw [hid, abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr hlL)]
    calc
      _ ≤ (1/n) * (L+2* |g|) :=
        mul_le_mul hgap hab (abs_nonneg _) (by positivity)
      _ = _ := by ring
  have hw0 : 0 < w := Real.rpow_pos_of_pos ht0 _
  have hw1 : 1 ≤ w := Real.one_le_rpow ht (by norm_num)
  have hw3 : w^3 = t := by
    dsimp [w]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]
    norm_num
  have hlog : L ≤ 3*w := by
    have h := Real.log_le_rpow_div ht0.le (by norm_num : (0 : ℝ) < 1/3)
    change L ≤ w / (1/3 : ℝ) at h
    linarith
  have hw2 : w^2 ≤ t := by rw [← hw3]; exact pow_le_pow_right₀ hw1 (by decide)
  have hwt : w ≤ t := by rw [← hw3]; exact le_self_pow₀ hw1 (by decide)
  have hmajor : ((L+2* |g|)/n)*w ≤ 6+4* |g| := by
    have hb := mul_le_mul_of_nonneg_right hlog hw0.le
    have hc := mul_le_mul_of_nonneg_left hwt (abs_nonneg g)
    have hd := mul_le_mul_of_nonneg_left ht2n (abs_nonneg g)
    calc
      _ = ((L+2* |g|)*w)/n := by ring
      _ ≤ _ := (div_le_iff₀ hn0).mpr (by nlinarith)
  exact (mul_le_mul_of_nonneg_right hpoly hw0.le).trans hmajor

/-- Every positive real cutoff is covered, including the empty finite sum.
The coefficient is deliberately coarse and explicit in the two known constants. -/
theorem doubleHarmonic_real_cutoff_error (t : ℝ) (ht : 0 < t) :
    |doubleHarmonic ⌊t⌋₊ -
      (Real.log t ^ 2 / 2 + 2 * Real.eulerMascheroniConstant * Real.log t +
        Real.eulerMascheroniConstant ^ 2 - 2 * firstStieltjesConstant)| ≤
      (1000 + 200 * |Real.eulerMascheroniConstant| +
        10 * Real.eulerMascheroniConstant ^ 2 + 20 * |firstStieltjesConstant|) *
        t ^ (-(1 / 3 : ℝ)) := by
  let g := Real.eulerMascheroniConstant
  let c := firstStieltjesConstant
  let E := 1000 + 200* |g| + 10*g^2 + 20* |c|
  let w := t ^ (1 / 3 : ℝ)
  have hw0 : 0 < w := Real.rpow_pos_of_pos ht _
  have hscaled : |doubleHarmonic ⌊t⌋₊ - quadraticKernelCenter g c t| * w ≤ E := by
    by_cases ht9 : 9 ≤ t
    · have hn9 : 9 ≤ ⌊t⌋₊ := (Nat.le_floor_iff ht.le).mpr (by exact_mod_cast ht9)
      have hn0 : 0 < (⌊t⌋₊ : ℝ) := by exact_mod_cast (show 0 < ⌊t⌋₊ by omega)
      have htn : t < (⌊t⌋₊ : ℝ)+1 := Nat.lt_floor_add_one t
      have hn1 : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast (show 1 ≤ ⌊t⌋₊ by omega)
      let v := (⌊t⌋₊ : ℝ) ^ (1 / 3 : ℝ)
      have hv0 : 0 ≤ v := Real.rpow_nonneg hn0.le _
      have hv3 : v^3 = (⌊t⌋₊ : ℝ) := by
        dsimp [v]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        norm_num
      have hw3 : w^3 = t := by
        dsimp [w]
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
        norm_num
      have hwv : w ≤ 2*v := by
        apply (Real.rpow_le_rpow_iff hw0.le (by positivity) (by norm_num : (0:ℝ)<3)).mp
        norm_num only [Real.rpow_ofNat]
        rw [mul_pow, hw3, hv3]
        norm_num
        linarith
      have hd := integer_kernel_error_scaled ⌊t⌋₊ hn9
      change |doubleHarmonic ⌊t⌋₊ - quadraticKernelCenter g c (⌊t⌋₊ : ℝ)| *v ≤ 40 at hd
      have hd80 : |doubleHarmonic ⌊t⌋₊ - quadraticKernelCenter g c (⌊t⌋₊ : ℝ)| *w ≤ 80 := by
        have h := mul_le_mul_of_nonneg_left hwv
          (abs_nonneg (doubleHarmonic ⌊t⌋₊ - quadraticKernelCenter g c (⌊t⌋₊ : ℝ)))
        nlinarith
      have hs := center_floor_shift_scaled g c t (by linarith)
      have htri := mul_le_mul_of_nonneg_right
        (abs_sub_le (doubleHarmonic ⌊t⌋₊)
          (quadraticKernelCenter g c (⌊t⌋₊ : ℝ)) (quadraticKernelCenter g c t)) hw0.le
      dsimp [w] at *
      dsimp [E]
      nlinarith [abs_nonneg g, abs_nonneg c, sq_nonneg g]
    · by_cases ht1 : 1 ≤ t
      · have hfloor8 : ⌊t⌋₊ ≤ 8 := by
          have hfloor : (⌊t⌋₊ : ℝ) < 9 := (Nat.floor_le ht.le).trans_lt (lt_of_not_ge ht9)
          have : ⌊t⌋₊ < 9 := by exact_mod_cast hfloor
          omega
        have hK := doubleHarmonic_nonneg_le_sq ⌊t⌋₊
        have hK64 : doubleHarmonic ⌊t⌋₊ ≤ 64 := by
          have h8 : (⌊t⌋₊ : ℝ) ≤ 8 := by exact_mod_cast hfloor8
          nlinarith [show (0 : ℝ) ≤ (⌊t⌋₊ : ℝ) from Nat.cast_nonneg _]
        have hlog0 : 0 ≤ Real.log t := Real.log_nonneg ht1
        have hlog9 : Real.log t ≤ 9 := (Real.log_le_sub_one_of_pos ht).trans (by linarith)
        have hw9 : w ≤ 9 := by
          have h := Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (1/3:ℝ)≤1)
          norm_num only [Real.rpow_one] at h
          exact h.trans (by linarith)
        have hcenter := quadraticKernelCenter_abs g c t
        rw [abs_of_nonneg hlog0] at hcenter
        have hnorm : |doubleHarmonic ⌊t⌋₊ - quadraticKernelCenter g c t| ≤
            209/2 + 18* |g| + g^2 + 2* |c| := by
          have htri := abs_sub (doubleHarmonic ⌊t⌋₊) (quadraticKernelCenter g c t)
          rw [abs_of_nonneg hK.1] at htri
          have hb := mul_le_mul_of_nonneg_left hlog9 (abs_nonneg g)
          nlinarith
        have hscaled := mul_le_mul hnorm hw9 hw0.le (by positivity :
          0 ≤ (209/2 : ℝ)+18* |g|+g^2+2* |c|)
        dsimp [E]
        nlinarith [abs_nonneg g, abs_nonneg c, sq_nonneg g]
      · have htlt : t < 1 := lt_of_not_ge ht1
        have hfloor : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr htlt
        have hK : doubleHarmonic ⌊t⌋₊ = 0 := by simp [hfloor, doubleHarmonic]
        have hw1 : w ≤ 1 := Real.rpow_le_one ht.le htlt.le (by norm_num)
        have hlinear : |Real.log t| *w ≤ 3 := by
          have h := (Real.abs_log_mul_self_rpow_lt t (1/3) ht htlt.le (by norm_num)).le
          norm_num only [one_div_div] at h
          simpa only [abs_mul, abs_of_pos hw0, w] using h
        let v := t ^ (1/6 : ℝ)
        have hv0 : 0 < v := Real.rpow_pos_of_pos ht _
        have hv2 : v^2 = w := (rpow_sixth_powers t ht.le).1
        have hsmall : |Real.log t| *v ≤ 6 := by
          have h := (Real.abs_log_mul_self_rpow_lt t (1/6) ht htlt.le (by norm_num)).le
          norm_num only [one_div_div] at h
          simpa only [abs_mul, abs_of_pos hv0, v] using h
        have hsquare : Real.log t ^ 2 * w ≤ 36 := by
          have hs := pow_le_pow_left₀ (by positivity : 0 ≤ |Real.log t| *v) hsmall 2
          calc
            _ ≤ (6 : ℝ)^2 := by simpa only [mul_pow, sq_abs, hv2] using hs
            _ = 36 := by norm_num
        have hcenter := mul_le_mul_of_nonneg_right (quadraticKernelCenter_abs g c t) hw0.le
        have hg := mul_le_mul_of_nonneg_left hlinear (abs_nonneg g)
        have hconst := mul_le_mul_of_nonneg_left hw1
          (by positivity : 0 ≤ g^2+2* |c|)
        rw [hK, zero_sub, abs_neg]
        dsimp [E]
        nlinarith [abs_nonneg g, abs_nonneg c, sq_nonneg g]
  have hdiv := (le_div_iff₀ hw0).mpr hscaled
  simpa only [quadraticKernelCenter, g, c, E, w, Real.rpow_neg ht.le,
    div_eq_mul_inv] using hdiv

end PrimePairConvolution



/-!
Finite-to-infinite error transfer for a kernel with a quadratic logarithmic
main term. This is the algebra and absolute-convergence step of Riesel--Vaughan
(1983), equations (3.5)--(3.8). The uniform kernel bound remains an explicit
input, and no coefficient moment value or numerical Euler bound is assumed.
-/

open scoped BigOperators

namespace PrimePairConvolution

theorem finiteKernelConvolution_eq_tsum
    (h : ArithmeticFunction ℝ) (K : ℕ → ℝ) (hK0 : K 0 = 0) (N : ℝ) :
    (∑ d ∈ Finset.Icc 1 ⌊N⌋₊, h d * K ⌊N / (d : ℝ)⌋₊) =
      ∑' d : ℕ, h d * K ⌊N / (d : ℝ)⌋₊ := by
  symm
  apply tsum_eq_sum
  intro d hd
  by_cases hd0 : d = 0
  · subst d
    simp
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    have hfloorlt : ⌊N⌋₊ < d := by
      simp only [Finset.mem_Icc, not_and] at hd
      exact lt_of_not_ge (hd hdpos)
    have hNd : N < (d : ℝ) := (Nat.floor_lt' hd0).mp hfloorlt
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hdpos
    have hz : ⌊N / (d : ℝ)⌋₊ = 0 :=
      Nat.floor_eq_zero.mpr ((div_lt_one hdR).mpr hNd)
    simp [hz, hK0]

/-- A positive power moment controls the full quadratic convolution error.
The three coefficient moments are actual convergent series. -/
theorem quadraticKernelConvolution_error_le
    (K : ℕ → ℝ) (hK0 : K 0 = 0)
    (A B D E β : ℝ) (hβ : 0 < β)
    (hK : ∀ t : ℝ, 0 < t →
      |K ⌊t⌋₊ - (A * Real.log t ^ 2 + B * Real.log t + D)| ≤ E * t ^ (-β))
    (h : ArithmeticFunction ℝ)
    (hw : Summable (fun n : ℕ => |h n| * (n : ℝ) ^ β))
    (N : ℝ) (hN : 0 < N) :
    |(∑ d ∈ Finset.Icc 1 ⌊N⌋₊, h d * K ⌊N / (d : ℝ)⌋₊) -
      ((A * Real.log N ^ 2 + B * Real.log N + D) * (∑' d : ℕ, h d) -
        (2 * A * Real.log N + B) * (∑' d : ℕ, h d * Real.log (d : ℝ)) +
        A * (∑' d : ℕ, h d * Real.log (d : ℝ)^2))| ≤
      E * N ^ (-β) * (∑' d : ℕ, |h d| * (d : ℝ)^β) := by
  have hnorm := logPower_norm_summable_of_weighted_summable h β hβ hw 0
  simp only [pow_zero, mul_one] at hnorm
  have hmass := hnorm.of_norm.hasSum
  have hlognorm := logPower_norm_summable_of_weighted_summable h β hβ hw 1
  simp only [pow_one] at hlognorm
  have hlog := hlognorm.of_norm.hasSum
  have hlog2 :=
    (logPower_norm_summable_of_weighted_summable h β hβ hw 2).of_norm.hasSum
  let R : ℕ → ℝ := fun d => h d *
    (K ⌊N / (d : ℝ)⌋₊ -
      (A * Real.log (N / (d : ℝ))^2 + B * Real.log (N / (d : ℝ)) + D))
  let C : ℝ := E * N ^ (-β)
  have hpoint : ∀ d : ℕ, ‖R d‖ ≤ C * (|h d| * (d : ℝ)^β) := by
    intro d
    by_cases hd0 : d = 0
    · subst d
      simp [R]
    · have hdR : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd0
      have hb := hK (N / (d : ℝ)) (div_pos hN hdR)
      have hpow : (N / (d : ℝ)) ^ (-β) = N ^ (-β) * (d : ℝ)^β := by
        rw [Real.div_rpow hN.le hdR.le, Real.rpow_neg hdR.le, div_inv_eq_mul]
      calc
        ‖R d‖ = |h d| * |K ⌊N / (d : ℝ)⌋₊ -
          (A * Real.log (N / (d : ℝ))^2 + B * Real.log (N / (d : ℝ)) + D)| := by
            dsimp only [R]
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ |h d| * (E * (N / (d : ℝ)) ^ (-β)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
        _ = C * (|h d| * (d : ℝ)^β) := by rw [hpow]; dsimp [C]; ring
  have hR : Summable R := (hw.mul_left C).of_norm_bounded hpoint
  have hbound : |∑' d : ℕ, R d| ≤ C * ∑' d : ℕ, |h d| * (d : ℝ)^β := by
    simpa only [Real.norm_eq_abs] using
      hR.hasSum.norm_le_of_bounded (hw.hasSum.mul_left C) hpoint
  have hdecomp :
      HasSum (fun d : ℕ => h d * K ⌊N / (d : ℝ)⌋₊)
        ((∑' d : ℕ, R d) +
          (A * Real.log N ^ 2 + B * Real.log N + D) * (∑' d : ℕ, h d) -
          (2 * A * Real.log N + B) * (∑' d : ℕ, h d * Real.log (d : ℝ)) +
          A * (∑' d : ℕ, h d * Real.log (d : ℝ)^2)) := by
    have hs := ((hR.hasSum.add
      (hmass.mul_left (A * Real.log N ^ 2 + B * Real.log N + D))).sub
      (hlog.mul_left (2 * A * Real.log N + B))).add (hlog2.mul_left A)
    apply hs.congr_fun
    intro d
    by_cases hd0 : d = 0
    · subst d
      simp [R]
    · dsimp [R]
      rw [Real.log_div hN.ne' (Nat.cast_ne_zero.mpr hd0)]
      ring
  have hcenter :
      (∑ d ∈ Finset.Icc 1 ⌊N⌋₊, h d * K ⌊N / (d : ℝ)⌋₊) -
        ((A * Real.log N ^ 2 + B * Real.log N + D) * (∑' d : ℕ, h d) -
          (2 * A * Real.log N + B) * (∑' d : ℕ, h d * Real.log (d : ℝ)) +
          A * (∑' d : ℕ, h d * Real.log (d : ℝ)^2)) = ∑' d : ℕ, R d := by
    rw [finiteKernelConvolution_eq_tsum h K hK0, hdecomp.tsum_eq]
    ring
  rw [hcenter]
  exact hbound

end PrimePairConvolution



/-!
The actual squarefree base coefficient has a quadratic logarithmic expansion.
All constants below are named actual convergent sums or constructed constants.
This is a local assembly, not an effective numerical threshold or the sharp
1.641 remainder of Riesel--Vaughan. No platform action is performed here.
-/

open scoped BigOperators

namespace PrimePairConvolution

noncomputable def cubicSecondLogMoment (h : ArithmeticFunction ℝ) : ℝ :=
  ∑' n : ℕ, h n * Real.log (n : ℝ)^2

noncomputable def cubicOneThirdMoment (h : ArithmeticFunction ℝ) : ℝ :=
  ∑' n : ℕ, |h n| * (n : ℝ)^(1 / 3 : ℝ)

noncomputable def primeLogQuotientSum : ℝ :=
  ∑' p : Nat.Primes, Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))

noncomputable def doubleHarmonicErrorConstant : ℝ :=
  1000 + 200 * |Real.eulerMascheroniConstant| +
    10 * Real.eulerMascheroniConstant^2 + 20 * |firstStieltjesConstant|

noncomputable def baseExpansionLinear : ℝ :=
  4 * Real.eulerMascheroniConstant + 4 * primeLogQuotientSum + Real.log 2

noncomputable def baseExpansionConstant (h : ArithmeticFunction ℝ) : ℝ :=
  2 * (Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant) +
    4 * Real.eulerMascheroniConstant * (2 * primeLogQuotientSum + Real.log 2 / 2) +
    TaoFivePrimes.twinPrimeConstant * cubicSecondLogMoment h

noncomputable def baseQuadraticCenter (h : ArithmeticFunction ℝ) (z : ℝ) : ℝ :=
  (Real.log z^2 + baseExpansionLinear * Real.log z + baseExpansionConstant h) /
    (2 * TaoFivePrimes.twinPrimeConstant)

private theorem correction_cubic_prime_values (p : ℕ) (hp : p.Prime) :
    correction p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      correction (p^2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      correction (p^3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2 := by
  simpa only [baseLocal] using And.intro (correction_prime p hp)
    (And.intro (correction_prime_sq p hp) (correction_prime_cube p hp))

private theorem correction_weighted_twoFifths_summable :
    Summable (fun n : ℕ => |correction n| * (n : ℝ)^(2 / 5 : ℝ)) :=
  weighted_summable_of_cubic_prime_power_values correction correction_isMultiplicative
    correction_cubic_prime_values correction_prime_power_zero

private theorem correction_weighted_oneThird_summable :
    Summable (fun n : ℕ => |correction n| * (n : ℝ)^(1 / 3 : ℝ)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _
    correction_weighted_twoFifths_summable
  intro n
  by_cases hn : n = 0
  · subst n
    simp
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1 / 3 : ℝ) ≤ 2 / 5))
      (abs_nonneg _)

/-- The error moment and signed second logarithmic moment are actual convergent
series for the same explicit correction used in the finite convolution. -/
theorem correction_expansion_moments_converge :
    HasSum (fun n : ℕ => |correction n| * (n : ℝ)^(1 / 3 : ℝ))
      (cubicOneThirdMoment correction) ∧
    Summable (fun n : ℕ => ‖correction n * Real.log (n : ℝ)^2‖) ∧
    HasSum (fun n : ℕ => correction n * Real.log (n : ℝ)^2)
      (cubicSecondLogMoment correction) := by
  have hlog := logPower_norm_summable_of_weighted_summable correction (2 / 5)
    (by norm_num) correction_weighted_twoFifths_summable 2
  exact ⟨correction_weighted_oneThird_summable.hasSum, hlog, hlog.of_norm.hasSum⟩

/-- A universal positive-real-cutoff expansion of the actual squarefree base
denominator, with named actual moments and no assumed convergence or error bound. -/
theorem baseCumulative_quadratic_error (z : ℝ) (hz : 0 < z) :
    |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
        if Squarefree n then ∏ p ∈ n.primeFactors, baseLocal p else 0) -
      baseQuadraticCenter correction z| ≤
      doubleHarmonicErrorConstant * cubicOneThirdMoment correction *
        z ^ (-(1 / 3 : ℝ)) := by
  have hkernel (t : ℝ) (ht : 0 < t) :
      |doubleHarmonic ⌊t⌋₊ -
        ((1 / 2 : ℝ) * Real.log t^2 + 2 * Real.eulerMascheroniConstant * Real.log t +
          (Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant))| ≤
        doubleHarmonicErrorConstant * t ^ (-(1 / 3 : ℝ)) := by
    have hp : (1 / 2 : ℝ) * Real.log t^2 +
        2 * Real.eulerMascheroniConstant * Real.log t +
        (Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant) =
        Real.log t^2 / 2 + 2 * Real.eulerMascheroniConstant * Real.log t +
          Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant := by ring
    rw [hp]
    exact doubleHarmonic_real_cutoff_error t ht
  have hconvolution :
      (∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
        if Squarefree n then ∏ p ∈ n.primeFactors, baseLocal p else 0) =
        ∑ d ∈ Finset.Icc 1 ⌊z⌋₊, correction d * doubleHarmonic ⌊z / (d : ℝ)⌋₊ := by
    simpa only [Nat.floor_div_natCast] using base_sum_eq_correction_doubleHarmonic ⌊z⌋₊
  have he := quadraticKernelConvolution_error_le doubleHarmonic
    (by simp [doubleHarmonic]) (1 / 2) (2 * Real.eulerMascheroniConstant)
    (Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant)
    doubleHarmonicErrorConstant (1 / 3) (by norm_num) hkernel
    correction correction_weighted_oneThird_summable z hz
  have hm : (∑' n : ℕ, correction n) = 1 / TaoFivePrimes.twinPrimeConstant :=
    (hasSum_reciprocal_twinPrimeConstant_of_cubic_prime_power_values correction
      correction_isMultiplicative correction_cubic_prime_values correction_prime_power_zero).tsum_eq
  have hl : (∑' n : ℕ, correction n * Real.log (n : ℝ)) =
      -((2 * primeLogQuotientSum + Real.log 2 / 2) / TaoFivePrimes.twinPrimeConstant) :=
    (cubic_logarithmic_moment_hasSum correction correction_isMultiplicative
      correction_cubic_prime_values correction_prime_power_zero).tsum_eq
  rw [hm, hl] at he
  have hC : TaoFivePrimes.twinPrimeConstant ≠ 0 := by
    have hb := TaoFivePrimes.twinPrimeConstant_bounds.1
    linarith
  have hcenter :
      ((1 / 2 : ℝ) * Real.log z^2 + 2 * Real.eulerMascheroniConstant * Real.log z +
        (Real.eulerMascheroniConstant^2 - 2 * firstStieltjesConstant)) *
          (1 / TaoFivePrimes.twinPrimeConstant) -
        (2 * (1 / 2 : ℝ) * Real.log z + 2 * Real.eulerMascheroniConstant) *
          (-((2 * primeLogQuotientSum + Real.log 2 / 2) / TaoFivePrimes.twinPrimeConstant)) +
        (1 / 2 : ℝ) * (∑' n : ℕ, correction n * Real.log (n : ℝ)^2) =
          baseQuadraticCenter correction z := by
    unfold baseQuadraticCenter baseExpansionLinear baseExpansionConstant cubicSecondLogMoment
    field_simp [hC] <;> ring
  rw [hcenter] at he
  rw [hconvolution]
  simpa only [cubicOneThirdMoment, mul_assoc, mul_left_comm, mul_comm] using he

end PrimePairConvolution



theorem solution :
    ∃ B E : ℝ, 0 ≤ E ∧ ∀ z : ℝ, 0 < z →
      |(∑ n ∈ Finset.Icc 1 ⌊z⌋₊,
          if Squarefree n then
            ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
          else 0) -
        (Real.log z ^ 2 +
          (4 * Real.eulerMascheroniConstant +
            4 * (∑' p : Nat.Primes,
              Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1))) + Real.log 2) *
            Real.log z + B) / (2 * TaoFivePrimes.twinPrimeConstant)| ≤
        E * z ^ (-(1 / 3 : ℝ)) := by
  refine ⟨PrimePairConvolution.baseExpansionConstant PrimePairConvolution.correction,
    PrimePairConvolution.doubleHarmonicErrorConstant *
      PrimePairConvolution.cubicOneThirdMoment PrimePairConvolution.correction, ?_, ?_⟩
  · apply mul_nonneg
    · unfold PrimePairConvolution.doubleHarmonicErrorConstant
      positivity
    · unfold PrimePairConvolution.cubicOneThirdMoment
      exact tsum_nonneg (fun n => mul_nonneg (abs_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  · intro z hz
    simpa only [PrimePairConvolution.baseLocal,
      PrimePairConvolution.baseQuadraticCenter, PrimePairConvolution.baseExpansionLinear,
      PrimePairConvolution.primeLogQuotientSum] using
      PrimePairConvolution.baseCumulative_quadratic_error z hz

#print axioms solution
