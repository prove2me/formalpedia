-- Prove2me | solution 1 for buchholz_double_factorial_constant_bound
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-06-23T21:40:43.323209+00:00
-- url     : https://prove2.me/submissions/1576274a-d809-40fa-b0d5-33a9539f07dc

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

open scoped BigOperators

theorem solution
    (n : ℕ) (hn : 1 ≤ n) :
    ((Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ)))
        ^ ((1 : ℝ) / (2 * n)) ≤ Real.sqrt 2 * Real.sqrt (2 * n) := by
  -- Core arithmetic fact (in ℕ): (2n)! ≤ (2n)^n · 2^n · n!.
  have key : ∀ m : ℕ, Nat.factorial (2 * m) ≤ (2 * m) ^ m * (2 ^ m * Nat.factorial m) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      -- (2(k+1))! = (2k+2) * (2k+1) * (2k)!
      have hfac : Nat.factorial (2 * (k + 1))
          = (2 * k + 2) * ((2 * k + 1) * Nat.factorial (2 * k)) := by
        have e1 : 2 * (k + 1) = (2 * k + 1) + 1 := by ring
        have e2 : 2 * k + 1 = (2 * k) + 1 := by ring
        rw [e1, Nat.factorial_succ, e2, Nat.factorial_succ]
      rw [hfac]
      -- bound (2k+1) ≤ (2k+2) and use ih on (2k)!
      have step1 :
          (2 * k + 2) * ((2 * k + 1) * Nat.factorial (2 * k))
            ≤ (2 * k + 2) * ((2 * k + 2) * ((2 * k) ^ k * (2 ^ k * Nat.factorial k))) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul
        · exact Nat.le_succ _
        · exact ih
      refine step1.trans ?_
      -- target RHS: g(k+1) = (2(k+1))^{k+1} * (2^{k+1} * (k+1)!)
      -- show (2k+2)*(2k+2)*(2k)^k*2^k*k! ≤ (2k+2)^{k+1}*2^{k+1}*(k+1)!
      have hpow : (2 * k) ^ k ≤ (2 * (k + 1)) ^ k := by
        apply Nat.pow_le_pow_left; omega
      have lhs_le :
          (2 * k + 2) * ((2 * k + 2) * ((2 * k) ^ k * (2 ^ k * Nat.factorial k)))
            ≤ (2 * k + 2) * ((2 * k + 2) * ((2 * (k + 1)) ^ k * (2 ^ k * Nat.factorial k))) := by
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_left
        apply Nat.mul_le_mul_right
        exact hpow
      refine lhs_le.trans ?_
      -- now pure rearrangement / identity with (k+1)! = (k+1)*k!
      have hfk : Nat.factorial (k + 1) = (k + 1) * Nat.factorial k := Nat.factorial_succ k
      -- RHS = (2(k+1))^{k+1} * (2^{k+1} * (k+1)!)
      have hrhs :
          (2 * (k + 1)) ^ (k + 1) * (2 ^ (k + 1) * Nat.factorial (k + 1))
            = (2 * k + 2) * (2 * (k + 1)) ^ k * (2 * 2 ^ k) * ((k + 1) * Nat.factorial k) := by
        rw [hfk]
        rw [pow_succ, pow_succ]
        ring
      rw [hrhs]
      -- LHS = (2k+2)*(2k+2)*(2(k+1))^k*2^k*k!
      -- RHS = (2k+2)*(2(k+1))^k*(2*2^k)*((k+1)*k!)
      -- both equal since 2k+2 = 2(k+1)
      have : (2 * k + 2) * ((2 * k + 2) * ((2 * (k + 1)) ^ k * (2 ^ k * Nat.factorial k)))
            = (2 * k + 2) * (2 * (k + 1)) ^ k * (2 * 2 ^ k) * ((k + 1) * Nat.factorial k) := by
        ring
      rw [this]
  -- Transfer to ℝ.
  have hnpos : 0 < n := hn
  have h2n_pos : (0 : ℝ) < 2 * n := by positivity
  -- positivity of denominator
  have hden_pos : (0 : ℝ) < (2 ^ n : ℝ) * (Nat.factorial n : ℝ) := by positivity
  -- pairCount = (2n)! / (2^n n!) ≥ 0
  set P : ℝ := (Nat.factorial (2 * n) : ℝ) / ((2 ^ n : ℝ) * (Nat.factorial n : ℝ)) with hP
  have hP_nonneg : 0 ≤ P := by
    rw [hP]; positivity
  -- P ≤ (2n)^n
  have hP_le : P ≤ ((2 * n : ℝ)) ^ n := by
    rw [hP, div_le_iff₀ hden_pos]
    -- (2n)! ≤ (2n)^n * (2^n * n!)
    have hkey := key n
    have : (Nat.factorial (2 * n) : ℝ)
        ≤ ((2 * n) ^ n * (2 ^ n * Nat.factorial n) : ℕ) := by
      exact_mod_cast hkey
    refine this.trans_eq ?_
    push_cast
    ring
  -- raise to 1/(2n): P^{1/2n} ≤ ((2n)^n)^{1/2n} = (2n)^{1/2} = √(2n)
  have hexp_nonneg : (0 : ℝ) ≤ (1 : ℝ) / (2 * n) := by positivity
  have step :
      P ^ ((1 : ℝ) / (2 * n)) ≤ (((2 * n : ℝ)) ^ n) ^ ((1 : ℝ) / (2 * n)) :=
    Real.rpow_le_rpow hP_nonneg hP_le hexp_nonneg
  -- simplify the RHS power:  ((2n)^n)^{1/(2n)} = (2n)^{1/2} = √(2n)
  have hrhs_eq : (((2 * n : ℝ)) ^ n) ^ ((1 : ℝ) / (2 * n)) = Real.sqrt (2 * n) := by
    rw [← Real.rpow_natCast ((2 * n : ℝ)) n, ← Real.rpow_mul (le_of_lt h2n_pos)]
    have hmul : (n : ℝ) * ((1 : ℝ) / (2 * n)) = (1 : ℝ) / 2 := by
      have hn_ne : (n : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hmul, ← Real.sqrt_eq_rpow]
  rw [hrhs_eq] at step
  -- finish: √(2n) ≤ √2·√(2n)
  refine step.trans ?_
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg (2 * (n : ℝ)), hsqrt2]
