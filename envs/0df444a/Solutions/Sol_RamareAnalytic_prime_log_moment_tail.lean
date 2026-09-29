-- Prove2me | solution 1 for RamareAnalytic.prime_log_moment_tail
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T20:57:48.568311+00:00
-- url     : https://prove2.me/submissions/0c9f20f1-d9eb-485f-bc33-2d66919cda3b

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

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

theorem solution (X : ℕ) (hX : 1 ≤ X) :
    Summable (fun p : ℕ =>
      if X < p ∧ p.Prime then Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ∧
    (∑' p : ℕ, if X < p ∧ p.Prime then
      Real.log (p : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ≤
      Real.log 4 * (1 / (X : ℝ) + 1 / ((X : ℝ) + 1)) := by
  exact RamareAnalytic.prime_log_moment_tail X hX

#print axioms solution
