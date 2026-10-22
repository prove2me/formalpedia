-- Prove2me | solution 1 for PowerTwoChoices.Limit.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:45:56.07875+00:00
-- url     : https://prove2.me/submissions/eab432c5-dcdf-44ac-892f-e4c869635b92

import Mathlib
import Definitions.Def_PowerTwoChoices_Limit_SupermarketSystem

set_option autoImplicit false
open scoped ENNReal
open Filter Topology PowerTwoChoices.Limit

theorem pow_sub_pow_abs_le (a b : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ n : ℕ, |a ^ n - b ^ n| ≤ n * |a - b| := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n+1) - b ^ (n+1) = a ^ n * (a - b) + b * (a ^ n - b ^ n) := by ring
    rw [e]
    have h1 : |a ^ n * (a - b)| ≤ |a - b| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg ha0 n)]
      exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ ha0 ha1)
    have h2 : |b * (a ^ n - b ^ n)| ≤ |a ^ n - b ^ n| := by
      rw [abs_mul, abs_of_nonneg hb0]
      exact mul_le_of_le_one_left (abs_nonneg _) hb1
    have h3 := abs_add_le (a ^ n * (a - b)) (b * (a ^ n - b ^ n))
    push_cast
    linarith

theorem solution (lam : ℝ) (d : ℕ) (hd : 2 ≤ d) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (x y : ℕ → ℝ) (hx : IsState x) (hy : IsState y) :
    (∑' i : ℕ, if 1 ≤ i then ENNReal.ofReal |drift lam d x i - drift lam d y i| else 0) ≤
      ENNReal.ofReal (2 + 2 * d * lam) * ∑' i : ℕ, ENNReal.ofReal |x i - y i| := by
  have hxi : ∀ i, 0 ≤ x i ∧ x i ≤ 1 := fun i =>
    ⟨hx.2.1 i, by simpa [hx.1] using hx.2.2 (Nat.zero_le i)⟩
  have hyi : ∀ i, 0 ≤ y i ∧ y i ≤ 1 := fun i =>
    ⟨hy.2.1 i, by simpa [hy.1] using hy.2.2 (Nat.zero_le i)⟩
  have hp : ∀ i, |x i ^ d - y i ^ d| ≤ d * |x i - y i| := fun i =>
    pow_sub_pow_abs_le _ _ (hxi i).1 (hxi i).2 (hyi i).1 (hyi i).2 d
  have hreal : ∀ j : ℕ, |drift lam d x (j+1) - drift lam d y (j+1)| ≤
      lam * d * (|x j - y j| + |x (j+1) - y (j+1)|) + |x (j+1) - y (j+1)| +
        |x (j+1+1) - y (j+1+1)| := by
    intro j
    unfold drift
    simp only [Nat.add_sub_cancel]
    have eqn : (lam * (x j ^ d - x (j+1) ^ d) - (x (j+1) - x (j+1+1))) -
        (lam * (y j ^ d - y (j+1) ^ d) - (y (j+1) - y (j+1+1))) =
        lam * ((x j ^ d - y j ^ d) - (x (j+1) ^ d - y (j+1) ^ d)) -
          ((x (j+1) - y (j+1)) - (x (j+1+1) - y (j+1+1))) := by ring
    rw [eqn]
    have h1 := abs_sub (lam * ((x j ^ d - y j ^ d) - (x (j+1) ^ d - y (j+1) ^ d)))
      ((x (j+1) - y (j+1)) - (x (j+1+1) - y (j+1+1)))
    have h2 : |lam * ((x j ^ d - y j ^ d) - (x (j+1) ^ d - y (j+1) ^ d))| ≤
        lam * (d * |x j - y j| + d * |x (j+1) - y (j+1)|) := by
      rw [abs_mul, abs_of_pos hlam0]
      apply mul_le_mul_of_nonneg_left _ hlam0.le
      exact (abs_sub _ _).trans (add_le_add (hp j) (hp (j+1)))
    have h3 := abs_sub (x (j+1) - y (j+1)) (x (j+1+1) - y (j+1+1))
    nlinarith [h1, h2, h3]
  set c : ℝ≥0∞ := ENNReal.ofReal (lam * d) with hc
  set ε : ℕ → ℝ≥0∞ := fun i => ENNReal.ofReal |x i - y i| with hε
  have hLHS : (∑' i : ℕ, if 1 ≤ i then ENNReal.ofReal |drift lam d x i - drift lam d y i| else 0) =
      ∑' j : ℕ, ENNReal.ofReal |drift lam d x (j+1) - drift lam d y (j+1)| := by
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp
  have hterm : ∀ j : ℕ, ENNReal.ofReal |drift lam d x (j+1) - drift lam d y (j+1)| ≤
      c * (ε j + ε (j+1)) + ε (j+1) + ε (j+1+1) := by
    intro j
    refine (ENNReal.ofReal_le_ofReal (hreal j)).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (abs_nonneg _),
      ENNReal.ofReal_add (by positivity) (abs_nonneg _),
      ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  have hS1 : ∑' j : ℕ, ε (j+1) ≤ ∑' j : ℕ, ε j :=
    ENNReal.tsum_comp_le_tsum_of_injective (f := fun j : ℕ => j + 1) (add_left_injective 1) ε
  have hS2 : ∑' j : ℕ, ε (j+1+1) ≤ ∑' j : ℕ, ε j :=
    ENNReal.tsum_comp_le_tsum_of_injective (f := fun j : ℕ => j + 1 + 1)
      (fun a b h => by simpa using h) ε
  have h2 : ENNReal.ofReal (2 + 2 * (d : ℝ) * lam) = 2 * c + 2 := by
    rw [show 2 + 2 * (d : ℝ) * lam = 2 * (lam * d) + 2 by ring,
      ENNReal.ofReal_add (by positivity) (by norm_num), ENNReal.ofReal_mul (by norm_num)]
    simp [hc]
  rw [hLHS, h2]
  calc ∑' j : ℕ, ENNReal.ofReal |drift lam d x (j+1) - drift lam d y (j+1)|
      ≤ ∑' j : ℕ, (c * (ε j + ε (j+1)) + ε (j+1) + ε (j+1+1)) := ENNReal.tsum_le_tsum hterm
    _ = c * (∑' j, ε j + ∑' j, ε (j+1)) + ∑' j, ε (j+1) + ∑' j, ε (j+1+1) := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ ≤ c * (∑' j, ε j + ∑' j, ε j) + ∑' j, ε j + ∑' j, ε j := by
        gcongr
    _ = (2 * c + 2) * ∑' j, ε j := by ring
