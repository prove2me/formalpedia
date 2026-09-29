-- Prove2me | solution 1 for PrimePairSieve.exists_base_double_harmonic_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T23:14:24.98731+00:00
-- url     : https://prove2.me/submissions/08b4af57-606e-411a-8296-381f224e815b

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

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


/-- One common coefficient for every local and finite identity. -/
theorem solution :
    ∃ h : ArithmeticFunction ℝ, h.IsMultiplicative ∧
    (∀ p : ℕ, Nat.Prime p →
      h p = (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) - 2 / (p : ℝ) ∧
      h (p ^ 2) = 1 / (p : ℝ)^2 -
        2 * (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ) ∧
      h (p ^ 3) =
        (if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)) / (p : ℝ)^2) ∧
    (∀ p k : ℕ, Nat.Prime p → 4 ≤ k → h (p ^ k) = 0) ∧
    (∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N,
        if Squarefree n then
          ∏ p ∈ n.primeFactors, if p = 2 then (1 : ℝ) else 2 / ((p : ℝ) - 2)
        else 0) =
      ∑ d ∈ Finset.Icc 1 N, h d *
        ∑ a ∈ Finset.Icc 1 (N / d), (harmonic ((N / d) / a) : ℝ) / (a : ℝ)) := by
  refine ⟨PrimePairConvolution.correction,
    PrimePairConvolution.correction_isMultiplicative, ?_, ?_, ?_⟩
  · intro p hp
    refine ⟨?_, ?_, ?_⟩
    · simpa only [PrimePairConvolution.baseLocal] using
        PrimePairConvolution.correction_prime p hp
    · simpa only [PrimePairConvolution.baseLocal] using
        PrimePairConvolution.correction_prime_sq p hp
    · simpa only [PrimePairConvolution.baseLocal] using
        PrimePairConvolution.correction_prime_cube p hp
  · exact PrimePairConvolution.correction_prime_power_zero
  · intro N
    simpa only [PrimePairConvolution.baseLocal, PrimePairConvolution.doubleHarmonic] using
      PrimePairConvolution.base_sum_eq_correction_doubleHarmonic N

#print axioms solution
