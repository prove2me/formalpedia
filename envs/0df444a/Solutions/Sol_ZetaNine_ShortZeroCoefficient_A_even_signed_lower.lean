-- Prove2me | solution 1 for ZetaNine.ShortZeroCoefficient.A_even_signed_lower
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-03T13:45:55.236827+00:00
-- url     : https://prove2.me/submissions/bf77e137-99c1-48e7-8a84-d81b5c03fb1c

import Definitions.Def_ZetaNine_ShortZeroCoefficient
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

/-!
The original short-zero coefficient is defined by its genuine binomial
finite sum. A direct differential-operator certificate proves the actual
Franel gamma expansion, and paired Euler operators preserve the positive
gamma cone through every factorial-normalized weighting block. The final
theorems give the all-even signed positivity, nonvanishing and explicit
quantitative lower bound for every `m`, without a gamma identity hypothesis.
These results concern `A`, not the nonvanishing or decay of `A*zeta(9)+B`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open Polynomial
open scoped BigOperators

section FranelCertificate
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace ZetaNine.FranelGamma

def theta (p : ℚ[X]) : ℚ[X] := X * derivative p

def gammaBasis (k t : ℕ) : ℚ[X] := X ^ k * (1 + X) ^ t

def franelOperator (n : ℕ) (p : ℚ[X]) : ℚ[X] :=
  theta (theta (theta p)) + X * theta (theta (theta p)) -
    C (3 * (n : ℚ)) * X * theta (theta p) +
    C (3 * (n : ℚ) ^ 2) * X * theta p - C ((n : ℚ) ^ 3) * X * p

def franelPolynomial (n : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (n + 1), monomial j ((n.choose j : ℚ) ^ 3)

def gammaCoefficient (n k : ℕ) : ℕ :=
  n.choose (2 * k) * (2 * k).choose k * (n + k).choose k

def gammaPolynomial (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    C (gammaCoefficient n k : ℚ) * gammaBasis k (n - 2 * k)

theorem theta_coeff (p : ℚ[X]) (j : ℕ) :
    (theta p).coeff j = (j : ℚ) * p.coeff j := by
  cases j with
  | zero => simp [theta]
  | succ j => simp [theta, Polynomial.coeff_X_mul, Polynomial.coeff_derivative, mul_comm]

theorem franelOperator_coeff_zero (n : ℕ) (p : ℚ[X]) :
    (franelOperator n p).coeff 0 = 0 := by
  simp [franelOperator, theta_coeff]

theorem franelOperator_coeff_succ (n : ℕ) (p : ℚ[X]) (j : ℕ) :
    (franelOperator n p).coeff (j + 1) =
      ((j : ℚ) + 1) ^ 3 * p.coeff (j + 1) -
        ((n : ℚ) - j) ^ 3 * p.coeff j := by
  simp only [franelOperator, mul_assoc, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, theta_coeff,
    Nat.cast_add, Nat.cast_one]
  ring

theorem franelOperator_kernel_unique (n : ℕ) (p q : ℚ[X])
    (hp : franelOperator n p = 0) (hq : franelOperator n q = 0)
    (hzero : p.coeff 0 = q.coeff 0) : p = q := by
  ext j
  induction j with
  | zero => exact hzero
  | succ j ih =>
    have hpj := congrArg (fun f : ℚ[X] => f.coeff (j + 1)) hp
    have hqj := congrArg (fun f : ℚ[X] => f.coeff (j + 1)) hq
    simp only [franelOperator_coeff_succ, Polynomial.coeff_zero] at hpj hqj
    have hj : ((j : ℚ) + 1) ^ 3 ≠ 0 := by positivity
    apply (mul_left_cancel₀ hj)
    rw [ih] at hpj
    linarith

theorem franelPolynomial_coeff (n j : ℕ) :
    (franelPolynomial n).coeff j = (n.choose j : ℚ) ^ 3 := by
  classical
  by_cases hj : j ≤ n
  · simp [franelPolynomial, Polynomial.finsetSum_coeff,
      Polynomial.coeff_monomial, Finset.mem_range, hj]
  · have hz := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj)
    simp [franelPolynomial, Polynomial.finsetSum_coeff,
      Polynomial.coeff_monomial, Finset.mem_range, hj, hz]

theorem franelOperator_franelPolynomial (n : ℕ) :
    franelOperator n (franelPolynomial n) = 0 := by
  ext j
  cases j with
  | zero => exact franelOperator_coeff_zero n _
  | succ j =>
    simp only [franelOperator_coeff_succ, franelPolynomial_coeff, Polynomial.coeff_zero]
    by_cases hj : j ≤ n
    · have h : (n.choose (j + 1) : ℚ) * ((j : ℚ) + 1) =
          (n.choose j : ℚ) * ((n : ℚ) - j) := by
        have hn := Nat.choose_succ_right_eq n j
        have hcast := congrArg (fun x : ℕ => (x : ℚ)) hn
        simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hj] using hcast
      nlinarith [congrArg (fun x : ℚ => x ^ 3) h]
    · have hz : n.choose j = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hj)
      have hzs : n.choose (j + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp only [hz, hzs, Nat.cast_zero, zero_pow (by decide : 3 ≠ 0),
        mul_zero, sub_self]

theorem theta_add (p q : ℚ[X]) : theta (p + q) = theta p + theta q := by
  simp [theta, mul_add]

theorem theta_C_mul (a : ℚ) (p : ℚ[X]) : theta (C a * p) = C a * theta p := by
  simp [theta, mul_left_comm]

theorem theta_X_pow (k : ℕ) : theta (X ^ k) = C (k : ℚ) * X ^ k := by
  cases k with
  | zero => simp [theta]
  | succ k =>
    rw [theta, Polynomial.derivative_X_pow_succ]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem theta_gammaBasis_succ (k t : ℕ) :
    theta (gammaBasis k (t + 1)) =
      C (k : ℚ) * gammaBasis k (t + 1) +
        C (t + 1 : ℚ) * gammaBasis (k + 1) t := by
  have hx := theta_X_pow k
  simp only [theta] at hx ⊢
  simp only [gammaBasis, Polynomial.derivative_mul, mul_add,
    Polynomial.derivative_pow_succ, Polynomial.derivative_add,
    Polynomial.derivative_one, Polynomial.derivative_X, zero_add, mul_one]
  rw [← mul_assoc, hx]
  simp only [pow_succ]
  ring

theorem theta_gammaBasis_zero (k : ℕ) :
    theta (gammaBasis k 0) = C (k : ℚ) * gammaBasis k 0 := by
  simp only [gammaBasis, pow_zero, mul_one, theta_X_pow]

theorem franelOperator_gammaBasis (k t : ℕ) :
    franelOperator (2 * k + t) (gammaBasis k t) =
      (1 - X) * (C ((k : ℚ) ^ 3) * gammaBasis k t -
        C (((3 * k + t + 1 : ℕ) : ℚ) * t * (t - 1 : ℕ)) *
          gammaBasis (k + 1) (t - 2)) := by
  unfold franelOperator
  cases t with
  | zero =>
    simp only [gammaBasis, pow_zero, mul_one, theta_X_pow, theta_C_mul,
      Nat.cast_zero, map_zero, zero_mul, mul_zero, add_zero,
      Nat.cast_mul, Nat.cast_ofNat]
    simp only [map_add, map_mul, map_ofNat, map_pow]
    ring
  | succ t =>
    cases t with
    | zero =>
      simp only [theta_gammaBasis_succ, theta_gammaBasis_zero, theta_add, theta_C_mul]
      simp only [gammaBasis, pow_zero, mul_one, theta_X_pow, theta_C_mul,
        Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero,
        Nat.sub_self, zero_mul, mul_zero, map_zero, add_zero, pow_succ]
      simp only [map_add, map_mul, map_one, map_zero, map_ofNat, map_pow]
      ring
    | succ t =>
      cases t with
      | zero =>
        simp only [theta_gammaBasis_succ, theta_gammaBasis_zero, theta_add, theta_C_mul]
        simp only [gammaBasis, pow_zero, mul_one, theta_X_pow, theta_C_mul,
          Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_zero,
          Nat.reduceSub, Nat.sub_self, zero_mul, mul_zero, map_zero, add_zero, pow_succ]
        simp only [map_add, map_mul, map_one, map_zero, map_ofNat, map_pow,
          Polynomial.C_1, Polynomial.C_0]
        norm_num
        ring
      | succ t =>
        simp only [theta_gammaBasis_succ, theta_add, theta_C_mul]
        simp only [gammaBasis, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
          Nat.cast_ofNat, Nat.succ_sub_succ_eq_sub, Nat.sub_zero, pow_succ]
        simp only [map_add, map_mul, map_one, map_ofNat, map_pow]
        ring

theorem gammaCoefficient_factorial (n k : ℕ) (hk : 2 * k ≤ n) :
    gammaCoefficient n k * k.factorial ^ 3 * (n - 2 * k).factorial =
      (n + k).factorial := by
  have h1 := Nat.choose_mul_factorial_mul_factorial hk
  have h2 : (2 * k).choose k * k.factorial * k.factorial = (2 * k).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
    have heq : 2 * k - k = k := by omega
    simpa only [heq] using h
  have h3 : (n + k).choose k * k.factorial * n.factorial = (n + k).factorial := by
    simpa only [Nat.add_sub_cancel] using
      Nat.choose_mul_factorial_mul_factorial (show k ≤ n + k by omega)
  calc
    _ = (n + k).choose k * k.factorial *
        (n.choose (2 * k) * ((2 * k).choose k * k.factorial * k.factorial) *
          (n - 2 * k).factorial) := by unfold gammaCoefficient; ring
    _ = (n + k).choose k * k.factorial *
        (n.choose (2 * k) * (2 * k).factorial * (n - 2 * k).factorial) := by rw [h2]
    _ = (n + k).choose k * k.factorial * n.factorial := by rw [h1]
    _ = (n + k).factorial := h3

theorem gammaCoefficient_step (n k : ℕ) :
    (k + 1) ^ 3 * gammaCoefficient n (k + 1) =
      (n + k + 1) * (n - 2 * k) * (n - 2 * k - 1) * gammaCoefficient n k := by
  by_cases hk : 2 * k ≤ n
  · by_cases hks : 2 * (k + 1) ≤ n
    · have hfac : (n - 2 * k).factorial =
          (n - 2 * k) * (n - 2 * k - 1) * (n - 2 * (k + 1)).factorial := by
        have ht : n - 2 * k = (n - 2 * (k + 1)) + 2 := by omega
        have ht1 : n - 2 * k - 1 = (n - 2 * (k + 1)) + 1 := by omega
        rw [ht]
        rw [show n - 2 * (k + 1) + 2 - 1 = n - 2 * (k + 1) + 1 by omega]
        simp only [Nat.factorial_succ]
        ring
      have hnext := gammaCoefficient_factorial n (k + 1) hks
      have hprev := gammaCoefficient_factorial n k hk
      apply Nat.mul_right_cancel
        (show 0 < k.factorial ^ 3 * (n - 2 * (k + 1)).factorial by positivity)
      calc
        _ = gammaCoefficient n (k + 1) * (k + 1).factorial ^ 3 *
            (n - 2 * (k + 1)).factorial := by rw [Nat.factorial_succ]; ring
        _ = (n + (k + 1)).factorial := hnext
        _ = (n + k + 1) * (n + k).factorial := by
          change (n + k + 1).factorial = (n + k + 1) * (n + k).factorial
          exact Nat.factorial_succ (n + k)
        _ = (n + k + 1) *
            (gammaCoefficient n k * k.factorial ^ 3 * (n - 2 * k).factorial) := by rw [hprev]
        _ = _ := by rw [hfac]; ring
    · have hzero : n.choose (2 * (k + 1)) = 0 :=
        Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hks)
      have hsmall : n - 2 * k = 0 ∨ n - 2 * k = 1 := by omega
      rcases hsmall with hsmall | hsmall <;> simp [gammaCoefficient, hzero, hsmall]
  · have hzero : n.choose (2 * k) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)
    have hzeros : n.choose (2 * (k + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [gammaCoefficient, hzero, hzeros]

theorem franelOperator_C_mul (n : ℕ) (a : ℚ) (p : ℚ[X]) :
    franelOperator n (C a * p) = C a * franelOperator n p := by
  ext j
  cases j with
  | zero => simp [franelOperator_coeff_zero]
  | succ j =>
    simp only [franelOperator_coeff_succ, Polynomial.coeff_C_mul]
    ring

theorem franelOperator_sum {ι : Type*} (n : ℕ) (S : Finset ι) (f : ι → ℚ[X]) :
    franelOperator n (∑ i ∈ S, f i) = ∑ i ∈ S, franelOperator n (f i) := by
  ext j
  cases j with
  | zero => simp [franelOperator_coeff_zero, Polynomial.finsetSum_coeff]
  | succ j =>
    simp only [franelOperator_coeff_succ, Polynomial.finsetSum_coeff,
      Finset.mul_sum, Finset.sum_sub_distrib]

def gammaStep (n k : ℕ) : ℚ[X] :=
  C ((k : ℚ) ^ 3 * (gammaCoefficient n k : ℚ)) * gammaBasis k (n - 2 * k)

theorem franelOperator_gammaTerm (n k : ℕ) (hk : 2 * k ≤ n) :
    franelOperator n (C (gammaCoefficient n k : ℚ) * gammaBasis k (n - 2 * k)) =
      (1 - X) * (gammaStep n k - gammaStep n (k + 1)) := by
  rw [franelOperator_C_mul]
  have hn : 2 * k + (n - 2 * k) = n := by omega
  have hgamma := franelOperator_gammaBasis k (n - 2 * k)
  rw [hn] at hgamma
  rw [hgamma]
  have hindex : 3 * k + (n - 2 * k) + 1 = n + k + 1 := by omega
  have htail : n - 2 * k - 2 = n - 2 * (k + 1) := by omega
  rw [hindex, htail]
  have hstep : ((k + 1 : ℕ) : ℚ) ^ 3 * (gammaCoefficient n (k + 1) : ℚ) =
      ((n + k + 1 : ℕ) : ℚ) * (n - 2 * k : ℕ) * (n - 2 * k - 1 : ℕ) *
        (gammaCoefficient n k : ℚ) := by
    exact_mod_cast gammaCoefficient_step n k
  unfold gammaStep
  rw [hstep]
  simp only [map_mul, map_pow]
  ring

theorem sum_range_difference (f : ℕ → ℚ[X]) (m : ℕ) :
    (∑ k ∈ Finset.range m, (f k - f (k + 1))) = f 0 - f m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring

theorem franelOperator_gammaPolynomial (n : ℕ) :
    franelOperator n (gammaPolynomial n) = 0 := by
  classical
  rw [gammaPolynomial, franelOperator_sum]
  have hterms : (∑ k ∈ Finset.range (n / 2 + 1),
      franelOperator n (C (gammaCoefficient n k : ℚ) * gammaBasis k (n - 2 * k))) =
      ∑ k ∈ Finset.range (n / 2 + 1),
        (1 - X) * (gammaStep n k - gammaStep n (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    apply franelOperator_gammaTerm
    have hk' := Finset.mem_range.mp hk
    omega
  rw [hterms, ← Finset.mul_sum, sum_range_difference]
  have hzero : n.choose (2 * (n / 2 + 1)) = 0 :=
    Nat.choose_eq_zero_of_lt (by omega)
  simp [gammaStep, gammaCoefficient, hzero]

theorem gammaBasis_coeff_zero (k t : ℕ) :
    (gammaBasis k t).coeff 0 = if k = 0 then 1 else 0 := by
  simp [gammaBasis, Polynomial.coeff_X_pow_mul', Polynomial.coeff_one_add_X_pow,
    eq_comm]

theorem gammaPolynomial_coeff_zero (n : ℕ) :
    (gammaPolynomial n).coeff 0 = 1 := by
  classical
  simp [gammaPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    gammaBasis_coeff_zero, gammaCoefficient]

theorem franelPolynomial_eq_gammaPolynomial (n : ℕ) :
    franelPolynomial n = gammaPolynomial n := by
  apply franelOperator_kernel_unique n _ _
    (franelOperator_franelPolynomial n) (franelOperator_gammaPolynomial n)
  simp [franelPolynomial_coeff, gammaPolynomial_coeff_zero]


end ZetaNine.FranelGamma

end FranelCertificate

namespace ZetaNine.ShortZeroCoefficient





/-- The polynomial whose value at `-1` gives the highest coefficient. -/
def H (n m r b : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (n + 1), monomial j (weightedCoeff n m r b j : ℚ)

theorem weightedCoeff_reflect (n m r b j : ℕ) (hj : j ≤ n) :
    weightedCoeff n m r b (n - j) = weightedCoeff n m r b j := by
  simp only [weightedCoeff, Nat.sub_sub_self hj, Nat.choose_symm hj]
  rw [Nat.mul_comm ((n - j + m).choose m)]

theorem H_coeff (n m r b j : ℕ) :
    (H n m r b).coeff j = if j ≤ n then (weightedCoeff n m r b j : ℚ) else 0 := by
  classical
  simp [H, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Finset.mem_range]

theorem H_eval_neg_one (n m r b : ℕ) :
    (H n m r b).eval (-1) =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * (weightedCoeff n m r b j : ℚ) := by
  simp [H, Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_comm]

theorem A_eq_eval (n m : ℕ) :
    (A n m : ℚ) = 28 * (-1 : ℚ) ^ m * (H n m 3 7).eval (-1) := by
  rw [H_eval_neg_one]
  simp only [A, Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Int.cast_pow,
    Int.cast_neg, Int.cast_one, Int.cast_natCast, pow_add]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]

theorem twenty_eight_dvd_A (n m : ℕ) : (28 : ℤ) ∣ A n m :=
  ⟨_, rfl⟩

/-- Euler's operator on actual polynomials. -/
def theta (p : ℚ[X]) : ℚ[X] := X * derivative p

theorem theta_coeff (p : ℚ[X]) (j : ℕ) :
    (theta p).coeff j = (j : ℚ) * p.coeff j := by
  cases j with
  | zero => simp [theta]
  | succ j => simp [theta, Polynomial.coeff_X_mul, Polynomial.coeff_derivative, mul_comm]

/-- The paired real-root operator `(theta+c)(n+c-theta)`. -/
def pairOperator (n : ℕ) (c : ℚ) (p : ℚ[X]) : ℚ[X] :=
  theta (C ((n : ℚ) + c) * p - theta p) +
    C c * (C ((n : ℚ) + c) * p - theta p)

theorem pairOperator_coeff (n : ℕ) (c : ℚ) (p : ℚ[X]) (j : ℕ) :
    (pairOperator n c p).coeff j =
      ((j : ℚ) + c) * ((n : ℚ) + c - j) * p.coeff j := by
  simp only [pairOperator, Polynomial.coeff_add, Polynomial.coeff_sub,
    theta_coeff, Polynomial.coeff_C_mul]
  ring

/-- One exact factorial-normalized block of all `m` paired operators. -/
def weightBlock (n : ℕ) : ℕ → ℚ[X] → ℚ[X]
  | 0, p => p
  | m + 1, p => C (((m + 1 : ℕ) : ℚ) ^ 2)⁻¹ *
      pairOperator n (m + 1 : ℕ) (weightBlock n m p)

private theorem cast_choose_step (j m : ℕ) :
    (((j + (m + 1)).choose (m + 1) : ℕ) : ℚ) =
      ((j : ℚ) + m + 1) / (m + 1) * ((j + m).choose m : ℚ) := by
  have h := Nat.add_one_mul_choose_eq (j + m) m
  have hcast : ((j : ℚ) + m + 1) * ((j + m).choose m : ℚ) =
      ((j + (m + 1)).choose (m + 1) : ℚ) * (m + 1) := by
    exact_mod_cast h
  have hne : (m + 1 : ℚ) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div]
  exact (eq_div_iff hne).mpr hcast.symm

theorem weightBlock_coeff (n m j : ℕ) (p : ℚ[X]) (hj : j ≤ n) :
    (weightBlock n m p).coeff j =
      ((j + m).choose m : ℚ) * ((n - j + m).choose m : ℚ) * p.coeff j := by
  induction m with
  | zero => simp [weightBlock]
  | succ m ih =>
    rw [weightBlock, Polynomial.coeff_C_mul, pairOperator_coeff, ih,
      cast_choose_step j m, cast_choose_step (n - j) m]
    have hjcast : ((n - j : ℕ) : ℚ) = (n : ℚ) - j := by
      exact Nat.cast_sub hj
    rw [hjcast]
    simp only [Nat.cast_add, Nat.cast_one]
    have hne : (m + 1 : ℚ) ≠ 0 := by positivity
    field_simp
    ring

/-- Arbitrarily many complete blocks, including the required seven. -/
def applyWeights (n m : ℕ) : ℕ → ℚ[X] → ℚ[X]
  | 0, p => p
  | b + 1, p => weightBlock n m (applyWeights n m b p)

theorem applyWeights_coeff (n m b j : ℕ) (p : ℚ[X]) (hj : j ≤ n) :
    (applyWeights n m b p).coeff j =
      (((j + m).choose m : ℚ) * ((n - j + m).choose m : ℚ)) ^ b * p.coeff j := by
  induction b with
  | zero => simp [applyWeights]
  | succ b ih =>
    rw [applyWeights, weightBlock_coeff n m j _ hj, ih, pow_succ]
    ring

theorem weightBlock_coeff_zero (n m j : ℕ) (p : ℚ[X]) (hj : p.coeff j = 0) :
    (weightBlock n m p).coeff j = 0 := by
  induction m with
  | zero => exact hj
  | succ m ih =>
    simp [weightBlock, Polynomial.coeff_C_mul, pairOperator_coeff, ih]

theorem applyWeights_coeff_zero (n m b j : ℕ) (p : ℚ[X]) (hj : p.coeff j = 0) :
    (applyWeights n m b p).coeff j = 0 := by
  induction b with
  | zero => exact hj
  | succ b ih => exact weightBlock_coeff_zero n m j _ ih

/-- This is the full polynomial identity needed in section 4 of the written note;
it is proved against the actual binomial coefficients for every parameter. -/
theorem H_eq_applyWeights (n m r b : ℕ) :
    H n m r b = applyWeights n m b (H n 0 r 0) := by
  ext j
  by_cases hj : j ≤ n
  · rw [H_coeff, if_pos hj, applyWeights_coeff n m b j _ hj,
      H_coeff, if_pos hj]
    simp only [weightedCoeff, Nat.add_zero, Nat.choose_zero_right, one_pow,
      mul_one, Nat.cast_mul, Nat.cast_pow]
    ring
  · rw [H_coeff, if_neg hj]
    symm
    apply applyWeights_coeff_zero
    rw [H_coeff, if_neg hj]

private theorem odd_sign_reflect (n j : ℕ) (hn : Odd n) (hj : j ≤ n) :
    (-1 : ℚ) ^ (n - j) = -(-1 : ℚ) ^ j := by
  have hprod : (-1 : ℚ) ^ (n - j) * (-1 : ℚ) ^ j = -1 := by
    rw [← pow_add, Nat.sub_add_cancel hj]
    exact hn.neg_one_pow
  have hsq : ((-1 : ℚ) ^ j) * ((-1 : ℚ) ^ j) = 1 := by
    rw [← mul_pow]
    simp
  have hne : (-1 : ℚ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_right_cancel₀ hne
  rw [hprod, neg_mul, hsq]

/-- The odd-degree zero control is proved for every `m`, `r`, and `b`,
using the genuine coefficient symmetry. This does not assert the even sign. -/
theorem H_odd_eval_zero (n m r b : ℕ) (hn : Odd n) :
    (H n m r b).eval (-1) = 0 := by
  rw [H_eval_neg_one]
  let s : ℚ := ∑ j ∈ Finset.range (n + 1),
    (-1 : ℚ) ^ j * (weightedCoeff n m r b j : ℚ)
  have hflip : (∑ j ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - j) * (weightedCoeff n m r b (n - j) : ℚ)) = s :=
    by simpa only [s] using
      Finset.sum_flip (n := n) (fun j =>
        (-1 : ℚ) ^ j * (weightedCoeff n m r b j : ℚ))
  have hneg : (∑ j ∈ Finset.range (n + 1),
      (-1 : ℚ) ^ (n - j) * (weightedCoeff n m r b (n - j) : ℚ)) = -s := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [weightedCoeff_reflect n m r b j hjn, odd_sign_reflect n j hn hjn]
    ring
  change s = 0
  linarith

theorem A_odd_zero (n m : ℕ) (hn : Odd n) : A n m = 0 := by
  have heq := A_eq_eval n m
  rw [H_odd_eval_zero n m 3 7 hn] at heq
  have h : (A n m : ℚ) = 0 := by simpa using heq
  exact_mod_cast h

/-- The classical gamma basis, parametrized by its index and remaining degree.
The total symmetric degree is `2*k+t`. -/
def gammaBasis (k t : ℕ) : ℚ[X] := X ^ k * (1 + X) ^ t

theorem theta_add (p q : ℚ[X]) : theta (p + q) = theta p + theta q := by
  simp [theta, mul_add]

theorem theta_C_mul (a : ℚ) (p : ℚ[X]) : theta (C a * p) = C a * theta p := by
  simp [theta, mul_left_comm]

theorem theta_X_pow (k : ℕ) : theta (X ^ k) = C (k : ℚ) * X ^ k := by
  cases k with
  | zero => simp [theta]
  | succ k =>
    rw [theta, Polynomial.derivative_X_pow_succ]
    simp only [pow_succ, Nat.cast_add, Nat.cast_one]
    ring

theorem theta_gammaBasis_succ (k t : ℕ) :
    theta (gammaBasis k (t + 1)) =
      C (k : ℚ) * gammaBasis k (t + 1) +
        C (t + 1 : ℚ) * gammaBasis (k + 1) t := by
  have hx := theta_X_pow k
  simp only [theta] at hx ⊢
  simp only [gammaBasis, Polynomial.derivative_mul, mul_add,
    Polynomial.derivative_pow_succ, Polynomial.derivative_add,
    Polynomial.derivative_one, Polynomial.derivative_X, zero_add, mul_one]
  rw [← mul_assoc, hx]
  simp only [pow_succ]
  ring

theorem pairOperator_eq_theta_square (n : ℕ) (c : ℚ) (p : ℚ[X]) :
    pairOperator n c p =
      C (c * ((n : ℚ) + c)) * p + C (n : ℚ) * theta p - theta (theta p) := by
  ext j
  simp only [pairOperator_coeff, Polynomial.coeff_sub, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, theta_coeff]
  ring

/-- The actual paired Euler operator has a positive triangular action in the
gamma basis. No real-root assumption is needed for this identity. -/
theorem pairOperator_gammaBasis (k t : ℕ) (c : ℚ) :
    pairOperator (2 * k + t) c (gammaBasis k t) =
      C (((k : ℚ) + c) * ((k + t : ℕ) + c)) * gammaBasis k t +
        C ((t : ℚ) * (t - 1 : ℕ)) * gammaBasis (k + 1) (t - 2) := by
  rw [pairOperator_eq_theta_square]
  cases t with
  | zero =>
    simp only [gammaBasis, pow_zero, mul_one, theta_X_pow, theta_C_mul,
      Nat.cast_zero, map_zero, zero_mul, add_zero,
      Nat.cast_mul, Nat.cast_ofNat]
    simp only [map_add, map_mul, map_ofNat]
    ring
  | succ t =>
    cases t with
    | zero =>
      simp only [theta_gammaBasis_succ, theta_add, theta_C_mul]
      simp only [gammaBasis, pow_zero, mul_one, theta_X_pow]
      simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
        Nat.cast_ofNat, Nat.cast_zero, Nat.sub_self, zero_mul, mul_zero,
        map_zero, add_zero, pow_zero, pow_succ]
      simp only [map_add, map_mul, map_one, map_ofNat, map_zero]
      ring
    | succ t =>
      rw [theta_gammaBasis_succ, theta_add, theta_C_mul, theta_C_mul,
        theta_gammaBasis_succ, theta_gammaBasis_succ]
      simp only [gammaBasis, Nat.cast_add, Nat.cast_mul, Nat.cast_one,
        Nat.cast_ofNat, Nat.succ_sub_succ_eq_sub,
        Nat.sub_zero, pow_succ]
      simp only [map_add, map_mul, map_one, map_ofNat]
      ring

theorem pairOperator_add (n : ℕ) (c : ℚ) (p q : ℚ[X]) :
    pairOperator n c (p + q) = pairOperator n c p + pairOperator n c q := by
  ext j
  simp only [pairOperator_coeff, Polynomial.coeff_add]
  ring

theorem pairOperator_C_mul (n : ℕ) (c a : ℚ) (p : ℚ[X]) :
    pairOperator n c (C a * p) = C a * pairOperator n c p := by
  ext j
  simp only [pairOperator_coeff, Polynomial.coeff_C_mul]
  ring

theorem pairOperator_zero (n : ℕ) (c : ℚ) : pairOperator n c 0 = 0 := by
  ext j
  simp [pairOperator_coeff]

/-- The cone of nonnegative gamma expansions in symmetric degree `2*d`.
This records a proved structural hypothesis; it does not assume any identity
for the original Franel polynomial. -/
inductive GammaCone (d : ℕ) : ℚ[X] → Prop
  | zero : GammaCone d 0
  | basis (k : ℕ) (hk : k ≤ d) : GammaCone d (gammaBasis k (2 * (d - k)))
  | add {p q : ℚ[X]} : GammaCone d p → GammaCone d q → GammaCone d (p + q)
  | mul {p : ℚ[X]} (a : ℚ) : 0 ≤ a → GammaCone d p → GammaCone d (C a * p)

def signedEval (d : ℕ) (p : ℚ[X]) : ℚ := (-1 : ℚ) ^ d * p.eval (-1)

theorem signedEval_zero (d : ℕ) : signedEval d 0 = 0 := by simp [signedEval]

theorem signedEval_add (d : ℕ) (p q : ℚ[X]) :
    signedEval d (p + q) = signedEval d p + signedEval d q := by
  simp [signedEval, mul_add]

theorem signedEval_C_mul (d : ℕ) (a : ℚ) (p : ℚ[X]) :
    signedEval d (C a * p) = a * signedEval d p := by
  simp [signedEval, mul_left_comm]

theorem signedEval_gammaBasis (d k : ℕ) (hk : k ≤ d) :
    signedEval d (gammaBasis k (2 * (d - k))) = if k = d then 1 else 0 := by
  by_cases hkd : k = d
  · subst k
    simp only [signedEval, gammaBasis, Nat.sub_self, mul_zero, pow_zero,
      mul_one, Polynomial.eval_pow, Polynomial.eval_X, if_true]
    rw [← mul_pow]
    norm_num
  · have ht : 0 < 2 * (d - k) := by omega
    simp [signedEval, gammaBasis, zero_pow (Nat.ne_of_gt ht), hkd]

theorem GammaCone.signedEval_nonneg {d : ℕ} {p : ℚ[X]} (hp : GammaCone d p) :
    0 ≤ signedEval d p := by
  induction hp with
  | zero => simp [signedEval_zero]
  | basis k hk => rw [signedEval_gammaBasis d k hk]; split <;> norm_num
  | add _ _ ihp ihq => rw [signedEval_add]; exact add_nonneg ihp ihq
  | mul a ha _ ih => rw [signedEval_C_mul]; exact mul_nonneg ha ih

/-- Positivity preservation for every paired operator follows directly from
its gamma action, without importing a real-root preservation theorem. -/
theorem GammaCone.pairOperator {d : ℕ} {p : ℚ[X]} (hp : GammaCone d p)
    (c : ℚ) (hc : 0 ≤ c) : GammaCone d (pairOperator (2 * d) c p) := by
  induction hp with
  | zero => rw [pairOperator_zero]; exact GammaCone.zero
  | basis k hk =>
    have hn : 2 * d = 2 * k + 2 * (d - k) := by omega
    rw [hn, pairOperator_gammaBasis]
    apply GammaCone.add
    · apply GammaCone.mul
      · positivity
      · exact GammaCone.basis k hk
    · by_cases hkd : k = d
      · subst k
        simp only [Nat.sub_self, mul_zero, Nat.cast_zero, zero_mul, map_zero]
        exact GammaCone.zero
      · have hnext : k + 1 ≤ d := by omega
        have ht : 2 * (d - k) - 2 = 2 * (d - (k + 1)) := by omega
        rw [ht]
        apply GammaCone.mul
        · positivity
        · exact GammaCone.basis (k + 1) hnext
  | add _ _ ihp ihq => rw [pairOperator_add]; exact GammaCone.add ihp ihq
  | mul a ha _ ih => rw [pairOperator_C_mul]; exact GammaCone.mul a ha ih

theorem GammaCone.weightBlock {d : ℕ} {p : ℚ[X]} (hp : GammaCone d p) (m : ℕ) :
    GammaCone d (weightBlock (2 * d) m p) := by
  induction m with
  | zero => exact hp
  | succ m ih =>
    apply GammaCone.mul
    · positivity
    · exact ih.pairOperator (m + 1 : ℕ) (by positivity)

theorem GammaCone.applyWeights {d : ℕ} {p : ℚ[X]} (hp : GammaCone d p)
    (m b : ℕ) : GammaCone d (applyWeights (2 * d) m b p) := by
  induction b with
  | zero => exact hp
  | succ b ih => exact ih.weightBlock m

/-- Each paired operator multiplies the signed endpoint by at least
`(d+c)^2`. This is the exact quantitative positivity bridge for section 6. -/
theorem GammaCone.pairOperator_signedEval_lower {d : ℕ} {p : ℚ[X]}
    (hp : GammaCone d p) (c : ℚ) (hc : 0 ≤ c) :
    ((d : ℚ) + c) ^ 2 * signedEval d p ≤
      signedEval d (ZetaNine.ShortZeroCoefficient.pairOperator (2 * d) c p) := by
  induction hp with
  | zero => simp [pairOperator_zero, signedEval_zero]
  | basis k hk =>
    by_cases hkd : k = d
    · subst k
      have hn : 2 * d = 2 * d + 0 := by omega
      simp only [Nat.sub_self, mul_zero]
      rw [hn, pairOperator_gammaBasis]
      simp only [Nat.cast_zero, zero_mul, map_zero, add_zero]
      rw [signedEval_C_mul]
      nlinarith
    · rw [signedEval_gammaBasis d k hk, if_neg hkd, mul_zero]
      exact ((GammaCone.basis k hk).pairOperator c hc).signedEval_nonneg
  | add _ _ ihp ihq =>
    rw [pairOperator_add, signedEval_add, signedEval_add]
    nlinarith
  | mul a ha _ ih =>
    rw [pairOperator_C_mul, signedEval_C_mul, signedEval_C_mul]
    nlinarith [mul_le_mul_of_nonneg_left ih ha]

/-- The factorial normalizer is accounted for exactly, for every block size. -/
theorem weightBlock_signedEval_lower {d : ℕ} {p : ℚ[X]} (hp : GammaCone d p)
    (m : ℕ) :
    ((d + m).choose m : ℚ) ^ 2 * signedEval d p ≤
      signedEval d (weightBlock (2 * d) m p) := by
  induction m with
  | zero => simp [weightBlock]
  | succ m ih =>
    rw [weightBlock, signedEval_C_mul]
    have hm : (m + 1 : ℚ) ≠ 0 := by positivity
    have hnorm : 0 ≤ (((m + 1 : ℕ) : ℚ) ^ 2)⁻¹ := by positivity
    have hchoose : ((d + (m + 1)).choose (m + 1) : ℚ) ^ 2 =
        (((m + 1 : ℕ) : ℚ) ^ 2)⁻¹ *
          ((d : ℚ) + (m + 1 : ℕ)) ^ 2 * ((d + m).choose m : ℚ) ^ 2 := by
      rw [cast_choose_step]
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    rw [hchoose]
    have hpair := (hp.weightBlock m).pairOperator_signedEval_lower
      (m + 1 : ℕ) (by positivity)
    calc
      _ = (((m + 1 : ℕ) : ℚ) ^ 2)⁻¹ *
          (((d : ℚ) + (m + 1 : ℕ)) ^ 2 *
            (((d + m).choose m : ℚ) ^ 2 * signedEval d p)) := by ring
      _ ≤ (((m + 1 : ℕ) : ℚ) ^ 2)⁻¹ *
          (((d : ℚ) + (m + 1 : ℕ)) ^ 2 *
            signedEval d (weightBlock (2 * d) m p)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ih (sq_nonneg _)) hnorm
      _ ≤ _ := mul_le_mul_of_nonneg_left hpair hnorm

/-- All repeated normalized blocks obey the lower bound, including `b=7`. -/
theorem applyWeights_signedEval_lower {d : ℕ} {p : ℚ[X]} (hp : GammaCone d p)
    (m b : ℕ) :
    ((d + m).choose m : ℚ) ^ (2 * b) * signedEval d p ≤
      signedEval d (applyWeights (2 * d) m b p) := by
  induction b with
  | zero => simp [applyWeights]
  | succ b ih =>
    rw [applyWeights]
    have hb := weightBlock_signedEval_lower (hp.applyWeights m b) m
    calc
      _ = ((d + m).choose m : ℚ) ^ 2 *
          (((d + m).choose m : ℚ) ^ (2 * b) * signedEval d p) := by
        rw [Nat.mul_add, Nat.mul_one, pow_add]
        ring
      _ ≤ ((d + m).choose m : ℚ) ^ 2 *
          signedEval d (applyWeights (2 * d) m b p) :=
        mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ ≤ _ := hb

/-- The explicit classical Franel gamma coefficient. -/
def gammaCoeff (n k : ℕ) : ℕ :=
  n.choose (2 * k) * (2 * k).choose k * (n + k).choose k

/-- The explicit gamma expansion. Its equality with the actual cubic-binomial
polynomial is a theorem below, rather than part of this definition. -/
def franelGamma (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    C (gammaCoeff n k : ℚ) * gammaBasis k (n - 2 * k)

theorem GammaCone.finsetSum {d : ℕ} (s : Finset ℕ) (f : ℕ → ℚ[X])
    (h : ∀ k ∈ s, GammaCone d (f k)) : GammaCone d (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GammaCone.zero (d := d)
  | @insert k s hks ih =>
    rw [Finset.sum_insert hks]
    exact GammaCone.add (h k (by simp))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

theorem signedEval_sum (d : ℕ) (s : Finset ℕ) (f : ℕ → ℚ[X]) :
    signedEval d (∑ k ∈ s, f k) = ∑ k ∈ s, signedEval d (f k) := by
  simp [signedEval, Polynomial.eval_finsetSum, Finset.mul_sum]

/-- The explicit gamma candidate belongs to the cone for every even degree. -/
theorem franelGamma_mem_cone (d : ℕ) : GammaCone d (franelGamma (2 * d)) := by
  have hn : 2 * d / 2 = d := by omega
  rw [franelGamma, hn]
  apply GammaCone.finsetSum
  intro k hk
  have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have ht : 2 * d - 2 * k = 2 * (d - k) := by omega
  rw [ht]
  exact GammaCone.mul _ (by positivity) (GammaCone.basis k hkd)

/-- The signed endpoint is exactly its top gamma coefficient. -/
theorem franelGamma_signedEval (d : ℕ) :
    signedEval d (franelGamma (2 * d)) =
      ((2 * d).choose d : ℚ) * ((3 * d).choose d : ℚ) := by
  have hn : 2 * d / 2 = d := by omega
  rw [franelGamma, hn, signedEval_sum]
  calc
    _ = ∑ k ∈ Finset.range (d + 1),
        if k = d then (gammaCoeff (2 * d) d : ℚ) else 0 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have ht : 2 * d - 2 * k = 2 * (d - k) := by omega
      rw [signedEval_C_mul, ht, signedEval_gammaBasis d k hkd]
      split <;> simp_all
    _ = (gammaCoeff (2 * d) d : ℚ) := by simp
    _ = _ := by
      have hd : 2 * d + d = 3 * d := by omega
      simp [gammaCoeff, hd]

theorem franelGamma_signedEval_pos (d : ℕ) : 0 < signedEval d (franelGamma (2 * d)) := by
  rw [franelGamma_signedEval]
  have htwo : 0 < (2 * d).choose d := Nat.choose_pos (by omega)
  have hthree : 0 < (3 * d).choose d := Nat.choose_pos (by omega)
  positivity

/-- Quantified positivity of every weighted gamma expansion. The final C3
proof transfers this bound to the genuine polynomial using `H_franel_identity`. -/
theorem weighted_franelGamma_signedEval_lower (d m b : ℕ) :
    ((d + m).choose m : ℚ) ^ (2 * b) *
      (((2 * d).choose d : ℚ) * ((3 * d).choose d : ℚ)) ≤
        signedEval d (applyWeights (2 * d) m b (franelGamma (2 * d))) := by
  rw [← franelGamma_signedEval]
  exact applyWeights_signedEval_lower (franelGamma_mem_cone d) m b

/-- Exact signed endpoint identity for the genuine integer coefficient. -/
theorem A_even_signed_cast_eq (d m : ℕ) :
    (-1 : ℚ) ^ (m + d) * (A (2 * d) m : ℚ) =
      28 * signedEval d (H (2 * d) m 3 7) := by
  rw [A_eq_eval, pow_add]
  have hm : (-1 : ℚ) ^ m * (-1 : ℚ) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  unfold signedEval
  calc
    _ = 28 * ((-1 : ℚ) ^ m * (-1 : ℚ) ^ m) *
          ((-1 : ℚ) ^ d * (H (2 * d) m 3 7).eval (-1)) := by ring
    _ = _ := by rw [hm]; ring

/-- The algebraic substitution used by the final C3 proof. The explicit
identity hypothesis here is discharged unconditionally by `H_franel_identity`
in the final signed and absolute lower-bound theorems. -/
theorem A_even_lower_of_franel_identity (d m : ℕ)
    (hF : H (2 * d) 0 3 0 = franelGamma (2 * d)) :
    (28 : ℤ) * ((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) *
        ((d + m).choose m : ℤ) ^ 14 ≤ (-1 : ℤ) ^ (m + d) * A (2 * d) m := by
  have hb := mul_le_mul_of_nonneg_left (weighted_franelGamma_signedEval_lower d m 7)
    (by norm_num : (0 : ℚ) ≤ 28)
  have heq : applyWeights (2 * d) m 7 (franelGamma (2 * d)) = H (2 * d) m 3 7 := by
    rw [H_eq_applyWeights, hF]
  rw [heq, ← A_even_signed_cast_eq] at hb
  norm_num at hb
  have hq : (28 : ℚ) * ((2 * d).choose d : ℚ) * ((3 * d).choose d : ℚ) *
        ((d + m).choose m : ℚ) ^ 14 ≤
      (-1 : ℚ) ^ (m + d) * (A (2 * d) m : ℚ) := by
    nlinarith [hb]
  exact_mod_cast hq

theorem A_even_signed_pos_of_franel_identity (d m : ℕ)
    (hF : H (2 * d) 0 3 0 = franelGamma (2 * d)) :
    0 < (-1 : ℤ) ^ (m + d) * A (2 * d) m := by
  have htwo : 0 < (2 * d).choose d := Nat.choose_pos (by omega)
  have hthree : 0 < (3 * d).choose d := Nat.choose_pos (by omega)
  have hweight : 0 < (d + m).choose m := Nat.choose_pos (by omega)
  have hpos : 0 < (28 : ℤ) * ((2 * d).choose d : ℤ) *
      ((3 * d).choose d : ℤ) * ((d + m).choose m : ℤ) ^ 14 := by positivity
  exact lt_of_lt_of_le hpos (A_even_lower_of_franel_identity d m hF)

theorem A_even_ne_zero_of_franel_identity (d m : ℕ)
    (hF : H (2 * d) 0 3 0 = franelGamma (2 * d)) : A (2 * d) m ≠ 0 := by
  have h := A_even_signed_pos_of_franel_identity d m hF
  intro hz
  rw [hz, mul_zero] at h
  exact lt_irrefl _ h

theorem A_even_abs_lower_of_franel_identity (d m : ℕ)
    (hF : H (2 * d) 0 3 0 = franelGamma (2 * d)) :
    (28 : ℤ) * ((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) *
        ((d + m).choose m : ℤ) ^ 14 ≤ |A (2 * d) m| := by
  calc
    _ ≤ (-1 : ℤ) ^ (m + d) * A (2 * d) m := A_even_lower_of_franel_identity d m hF
    _ ≤ |(-1 : ℤ) ^ (m + d) * A (2 * d) m| := le_abs_self _
    _ = _ := by rw [abs_mul, abs_pow]; norm_num

/-- This low-degree identity is also checked directly by polynomial algebra;
the following infinite `m` family provides an independent simple example. -/
theorem H_two_franel_identity : H 2 0 3 0 = franelGamma 2 := by
  norm_num [H, weightedCoeff, franelGamma, gammaCoeff, gammaBasis,
    Finset.sum_range_succ, ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

theorem A_two_signed_lower (m : ℕ) :
    (168 : ℤ) * ((m + 1 : ℕ) : ℤ) ^ 14 ≤ (-1 : ℤ) ^ (m + 1) * A 2 m := by
  have h := A_even_lower_of_franel_identity 1 m H_two_franel_identity
  simpa [Nat.add_comm, Nat.choose_succ_self_right] using h

theorem A_two_ne_zero (m : ℕ) : A 2 m ≠ 0 := by
  have h := A_two_signed_lower m
  have hp : 0 < (168 : ℤ) * ((m + 1 : ℕ) : ℤ) ^ 14 := by positivity
  intro hz
  rw [hz, mul_zero] at h
  omega

/-- Connect the genuine cubic-binomial polynomial to the independently
certified Franel polynomial by its actual coefficients. -/
theorem H_franel_eq_certificate (n : ℕ) :
    H n 0 3 0 = ZetaNine.FranelGamma.franelPolynomial n := by
  unfold H ZetaNine.FranelGamma.franelPolynomial
  apply Finset.sum_congr rfl
  intro j _
  simp [weightedCoeff]

/-- The genuine Franel gamma identity, now proved for every degree. -/
theorem H_franel_identity (n : ℕ) : H n 0 3 0 = franelGamma n := by
  calc
    _ = ZetaNine.FranelGamma.franelPolynomial n := H_franel_eq_certificate n
    _ = ZetaNine.FranelGamma.gammaPolynomial n :=
      ZetaNine.FranelGamma.franelPolynomial_eq_gammaPolynomial n
    _ = _ := rfl

/-- Full C3: the exact signed lower bound, for all even degrees and all `m`. -/
theorem checked_A_even_signed_lower (d m : ℕ) :
    (28 : ℤ) * ((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) *
        ((d + m).choose m : ℤ) ^ 14 ≤ (-1 : ℤ) ^ (m + d) * A (2 * d) m :=
  A_even_lower_of_franel_identity d m (H_franel_identity (2 * d))

/-- Full C3 has no restriction on `m`; it even includes degree zero. -/
theorem A_even_signed_pos (d m : ℕ) : 0 < (-1 : ℤ) ^ (m + d) * A (2 * d) m :=
  A_even_signed_pos_of_franel_identity d m (H_franel_identity (2 * d))

theorem A_even_ne_zero (d m : ℕ) : A (2 * d) m ≠ 0 :=
  A_even_ne_zero_of_franel_identity d m (H_franel_identity (2 * d))

/-- The original coefficient's fully explicit all-parameter magnitude bound. -/
theorem A_even_abs_lower (d m : ℕ) :
    (28 : ℤ) * ((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) *
        ((d + m).choose m : ℤ) ^ 14 ≤ |A (2 * d) m| :=
  A_even_abs_lower_of_franel_identity d m (H_franel_identity (2 * d))

theorem A_signed_pos_of_even (n m : ℕ) (hn : Even n) :
    0 < (-1 : ℤ) ^ (m + n / 2) * A n m := by
  obtain ⟨d, hd⟩ := hn
  have hn' : n = 2 * d := by omega
  have hdiv : n / 2 = d := by omega
  rw [hdiv, hn']
  exact A_even_signed_pos d m

theorem A_ne_zero_of_even (n m : ℕ) (hn : Even n) : A n m ≠ 0 := by
  have hp := A_signed_pos_of_even n m hn
  intro hz
  rw [hz, mul_zero] at hp
  exact lt_irrefl _ hp

/-- The elementary Dixon constant is itself given by a factorial identity. -/
theorem dixon_constant_factorial (d : ℕ) :
    ((2 * d).choose d * (3 * d).choose d) * d.factorial ^ 3 = (3 * d).factorial := by
  have h := ZetaNine.FranelGamma.gammaCoefficient_factorial (2 * d) d (by omega)
  have hn : 2 * d + d = 3 * d := by omega
  simpa [ZetaNine.FranelGamma.gammaCoefficient, hn] using h

/-- The terminating even Dixon sum is proved from the genuine Franel identity,
without importing a hypergeometric evaluation as an assumption. -/
theorem franel_alternating_sum_even (d : ℕ) :
    (∑ j ∈ Finset.range (2 * d + 1),
      (-1 : ℤ) ^ j * ((2 * d).choose j : ℤ) ^ 3) =
        (-1 : ℤ) ^ d * ((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) := by
  have h := franelGamma_signedEval d
  rw [← H_franel_identity, signedEval, H_eval_neg_one] at h
  simp only [weightedCoeff, Nat.add_zero, Nat.choose_zero_right,
    mul_one, one_pow, Nat.cast_pow] at h
  have hs : (-1 : ℚ) ^ d * (-1 : ℚ) ^ d = 1 := by
    rw [← mul_pow]
    norm_num
  have hq : (∑ j ∈ Finset.range (2 * d + 1),
      (-1 : ℚ) ^ j * ((2 * d).choose j : ℚ) ^ 3) =
        (-1 : ℚ) ^ d * ((2 * d).choose d : ℚ) * ((3 * d).choose d : ℚ) := by
    calc
      _ = ((-1 : ℚ) ^ d * (-1 : ℚ) ^ d) *
          (∑ j ∈ Finset.range (2 * d + 1),
            (-1 : ℚ) ^ j * ((2 * d).choose j : ℚ) ^ 3) := by rw [hs, one_mul]
      _ = (-1 : ℚ) ^ d * ((-1 : ℚ) ^ d *
          (∑ j ∈ Finset.range (2 * d + 1),
            (-1 : ℚ) ^ j * ((2 * d).choose j : ℚ) ^ 3)) := by ring
      _ = _ := by rw [h]; ring
  exact_mod_cast hq

theorem A_even_unweighted (d : ℕ) :
    A (2 * d) 0 = (28 : ℤ) * (-1 : ℤ) ^ d *
      ((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) := by
  simp only [A, weightedCoeff, Nat.add_zero, Nat.zero_add, Nat.choose_zero_right,
    mul_one, one_pow, Nat.cast_pow]
  rw [franel_alternating_sum_even]
  ring

theorem A_even_abs_ge_twenty_eight (d m : ℕ) : (28 : ℤ) ≤ |A (2 * d) m| := by
  have htwo : 0 < (2 * d).choose d := Nat.choose_pos (by omega)
  have hthree : 0 < (3 * d).choose d := Nat.choose_pos (by omega)
  have hweight : 0 < (d + m).choose m := Nat.choose_pos (by omega)
  have hprod : 0 < ((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) *
      ((d + m).choose m : ℤ) ^ 14 := by positivity
  have hprod1 : 1 ≤ ((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) *
      ((d + m).choose m : ℤ) ^ 14 := by omega
  calc
    (28 : ℤ) ≤ 28 * (((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) *
        ((d + m).choose m : ℤ) ^ 14) := by
      simpa using mul_le_mul_of_nonneg_left hprod1 (by norm_num : (0 : ℤ) ≤ 28)
    _ = 28 * ((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) *
        ((d + m).choose m : ℤ) ^ 14 := by ring
    _ ≤ _ := A_even_abs_lower d m

theorem A_abs_ge_twenty_eight_of_even (n m : ℕ) (hn : Even n) :
    (28 : ℤ) ≤ |A n m| := by
  obtain ⟨d, hd⟩ := hn
  have hn' : n = 2 * d := by omega
  rw [hn']
  exact A_even_abs_ge_twenty_eight d m

end ZetaNine.ShortZeroCoefficient


open ZetaNine.ShortZeroCoefficient

theorem solution (d m : ℕ) :
    (28 : ℤ) * ((2 * d).choose d : ℤ) * ((3 * d).choose d : ℤ) *
        ((d + m).choose m : ℤ) ^ 14 ≤ (-1 : ℤ) ^ (m + d) * A (2 * d) m := by
  exact ZetaNine.ShortZeroCoefficient.checked_A_even_signed_lower d m

#print axioms solution
