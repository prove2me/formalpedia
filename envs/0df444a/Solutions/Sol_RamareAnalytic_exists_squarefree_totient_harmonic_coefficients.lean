-- Prove2me | solution 1 for RamareAnalytic.exists_squarefree_totient_harmonic_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T20:46:21.643059+00:00
-- url     : https://prove2.me/submissions/8b0cf07b-6e31-4407-b66a-9d6c1b8bc76f

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

set_option autoImplicit false

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.Moebius

namespace RamareAnalytic

/-!
Finite algebra for Ramaré's correction coefficients, equation (3.7) and the
convolution underlying (3.8), printed p.659 of the 1995 paper.
Every definition is an explicit arithmetic operation. There is no field
assuming convolution, multiplicativity, a prime-power value, or an estimate.
No convergence, Euler product, or analytic remainder is asserted here.
-/

noncomputable def squarefreeTotient : ArithmeticFunction ℝ :=
  ⟨fun n => if Squarefree n then 1 / (Nat.totient n : ℝ) else 0, by simp⟩

@[simp] theorem squarefreeTotient_apply (n : ℕ) :
    squarefreeTotient n = if Squarefree n then 1 / (Nat.totient n : ℝ) else 0 := rfl

noncomputable def divideByNat (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f.pdiv (ArithmeticFunction.id : ArithmeticFunction ℝ)

@[simp] theorem divideByNat_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    divideByNat f n = f n / (n : ℝ) := by
  simp [divideByNat]

/-- Pointwise division by n respects Dirichlet convolution. -/
theorem divideByNat_mul (f g : ArithmeticFunction ℝ) :
    divideByNat (f * g) = divideByNat f * divideByNat g := by
  ext n
  simp only [divideByNat_apply, ArithmeticFunction.mul_apply, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ab hab
  have he : (ab.1 : ℝ) * (ab.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast (Nat.mem_divisorsAntidiagonal.mp hab).1
  rw [← he, div_mul_div_comm]

@[simp] theorem divideByNat_one :
    divideByNat (1 : ArithmeticFunction ℝ) = 1 := by
  ext n
  by_cases hn : n = 1 <;> simp [ArithmeticFunction.one_apply, hn]

theorem divideByNat_isMultiplicative (f : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) : (divideByNat f).IsMultiplicative :=
  hf.pdiv ArithmeticFunction.isMultiplicative_id.natCast

theorem squarefreeTotient_isMultiplicative : squarefreeTotient.IsMultiplicative := by
  refine ⟨by simp, ?_⟩
  intro m n hcop
  simp only [squarefreeTotient_apply, Nat.squarefree_mul hcop,
    Nat.totient_mul hcop, Nat.cast_mul]
  by_cases hm : Squarefree m <;> by_cases hn : Squarefree n <;>
    simp [hm, hn, one_div, mul_inv, mul_comm]

noncomputable def weightedSquarefreeTotient : ArithmeticFunction ℝ :=
  (ArithmeticFunction.id : ArithmeticFunction ℝ).pmul squarefreeTotient

@[simp] theorem weightedSquarefreeTotient_apply (n : ℕ) :
    weightedSquarefreeTotient n = (n : ℝ) * squarefreeTotient n := by
  simp [weightedSquarefreeTotient]

@[simp] theorem divideByNat_weightedSquarefreeTotient :
    divideByNat weightedSquarefreeTotient = squarefreeTotient := by
  ext n
  by_cases hn : n = 0
  · subst n
    simp
  · rw [divideByNat_apply, weightedSquarefreeTotient_apply]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hn)

noncomputable def harmonicKernel : ArithmeticFunction ℝ :=
  divideByNat (ζ : ArithmeticFunction ℝ)

@[simp] theorem harmonicKernel_apply (n : ℕ) :
    harmonicKernel n = 1 / (n : ℝ) := by
  by_cases hn : n = 0 <;> simp [harmonicKernel, hn]

/-- Explicit Möbius deconvolution followed by division by n. -/
noncomputable def correction : ArithmeticFunction ℝ :=
  divideByNat (weightedSquarefreeTotient * (μ : ArithmeticFunction ℝ))

theorem correction_isMultiplicative : correction.IsMultiplicative := by
  apply divideByNat_isMultiplicative
  exact (ArithmeticFunction.isMultiplicative_id.natCast.pmul
    squarefreeTotient_isMultiplicative).mul
      ArithmeticFunction.isMultiplicative_moebius.intCast

/-- The exact source convolution, valid as equality of arithmetic functions. -/
theorem correction_convolution :
    correction * harmonicKernel = squarefreeTotient := by
  unfold correction harmonicKernel
  rw [← divideByNat_mul, mul_assoc,
    ArithmeticFunction.coe_moebius_mul_coe_zeta, mul_one]
  exact divideByNat_weightedSquarefreeTotient

private theorem Ioc_zero_eq_Icc_one (N : ℕ) :
    Finset.Ioc 0 N = Finset.Icc 1 N := by
  ext n
  simp only [Finset.mem_Ioc, Finset.mem_Icc]
  omega

private theorem harmonicKernel_sum (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, harmonicKernel n) = (harmonic N : ℝ) := by
  rw [Ioc_zero_eq_Icc_one, harmonic_eq_sum_Icc]
  simp [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

/-- Finite harmonic convolution at every integer cutoff, including zero. -/
theorem sum_squarefreeTotient_eq_correction_harmonic (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
      if Squarefree n then (1 : ℝ) / Nat.totient n else 0) =
      ∑ d ∈ Finset.Icc 1 N, correction d * (harmonic (N / d) : ℝ) := by
  have hs := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum correction harmonicKernel N
  rw [correction_convolution] at hs
  simp_rw [harmonicKernel_sum] at hs
  simpa only [Ioc_zero_eq_Icc_one, squarefreeTotient_apply] using hs

private theorem mul_moebius_prime_power (f : ArithmeticFunction ℝ) (p k : ℕ)
    (hp : Nat.Prime p) :
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

@[simp] theorem squarefreeTotient_prime (p : ℕ) (hp : Nat.Prime p) :
    squarefreeTotient p = 1 / ((p : ℝ) - 1) := by
  simp [hp.squarefree, Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le]

theorem squarefreeTotient_prime_power_zero (p k : ℕ) (hp : Nat.Prime p)
    (hk : 2 ≤ k) : squarefreeTotient (p ^ k) = 0 := by
  have hn : ¬ Squarefree (p ^ k) := by
    rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
    simp [show k ≠ 1 by omega]
  simp [hn]

private theorem weighted_prime_power_zero (p k : ℕ) (hp : Nat.Prime p)
    (hk : 2 ≤ k) : weightedSquarefreeTotient (p ^ k) = 0 := by
  simp [squarefreeTotient_prime_power_zero p k hp hk]

theorem correction_prime (p : ℕ) (hp : Nat.Prime p) :
    correction p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hm :
      (weightedSquarefreeTotient * (μ : ArithmeticFunction ℝ)) p =
        weightedSquarefreeTotient p - weightedSquarefreeTotient 1 := by
    simpa using mul_moebius_prime_power weightedSquarefreeTotient p 0 hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have htwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  unfold correction
  rw [divideByNat_apply, hm]
  simp only [weightedSquarefreeTotient_apply, squarefreeTotient_prime p hp]
  norm_num
  field_simp [hp0, hp1] <;> ring

theorem correction_prime_sq (p : ℕ) (hp : Nat.Prime p) :
    correction (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))) := by
  have hm :
      (weightedSquarefreeTotient * (μ : ArithmeticFunction ℝ)) (p ^ 2) =
        weightedSquarefreeTotient (p ^ 2) - weightedSquarefreeTotient p := by
    simpa using mul_moebius_prime_power weightedSquarefreeTotient p 1 hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have htwo : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  unfold correction
  rw [divideByNat_apply, hm, weighted_prime_power_zero p 2 hp (by omega)]
  simp only [weightedSquarefreeTotient_apply, squarefreeTotient_prime p hp, Nat.cast_pow]
  field_simp [hp0, hp1] <;> ring

theorem correction_prime_power_zero (p k : ℕ) (hp : Nat.Prime p)
    (hk : 3 ≤ k) : correction (p ^ k) = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    unfold correction
    rw [divideByNat_apply, mul_moebius_prime_power weightedSquarefreeTotient p k hp,
      weighted_prime_power_zero p (k + 1) hp (by omega),
      weighted_prime_power_zero p k hp (by omega)]
    simp

end RamareAnalytic

theorem solution :
    ∃ h : ArithmeticFunction ℝ, h.IsMultiplicative ∧
    (∀ p : ℕ, Nat.Prime p →
      h p = 1 / ((p : ℝ) * ((p : ℝ) - 1)) ∧
      h (p ^ 2) = -(1 / ((p : ℝ) * ((p : ℝ) - 1)))) ∧
    (∀ p k : ℕ, Nat.Prime p → 3 ≤ k → h (p ^ k) = 0) ∧
    (∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N,
        if Squarefree n then (1 : ℝ) / Nat.totient n else 0) =
      ∑ d ∈ Finset.Icc 1 N, h d * (harmonic (N / d) : ℝ)) := by
  refine ⟨RamareAnalytic.correction, RamareAnalytic.correction_isMultiplicative,
    ?_, ?_, RamareAnalytic.sum_squarefreeTotient_eq_correction_harmonic⟩
  · intro p hp
    exact ⟨RamareAnalytic.correction_prime p hp, RamareAnalytic.correction_prime_sq p hp⟩
  · intro p k hp hk
    exact RamareAnalytic.correction_prime_power_zero p k hp hk

#print axioms solution
