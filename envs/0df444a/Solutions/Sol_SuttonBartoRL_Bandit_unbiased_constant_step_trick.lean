-- Prove2me | solution 1 for SuttonBartoRL.Bandit.unbiased_constant_step_trick
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:46:13.987131+00:00
-- url     : https://prove2.me/submissions/4f6cd1a2-19ff-46c5-aaaf-ab6672fa6c42

import Mathlib
import Definitions.Def_SuttonBartoRL_Bandit_IncrementalEstimates

set_option autoImplicit false

open SuttonBartoRL.Bandit in
theorem p093_trace_eq (α : ℝ) (n : ℕ) : traceOfOne α n = 1 - (1 - α) ^ n := by
  induction n with
  | zero => simp [traceOfOne]
  | succ k ih => rw [traceOfOne, ih]; ring

open SuttonBartoRL.Bandit in
theorem p093_trace_pos (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    0 < traceOfOne α n := by
  rw [p093_trace_eq]
  have h : (1 - α) ^ n < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  linarith

theorem p093_sum_succ (α : ℝ) (R : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 (n + 1), α * (1 - α) ^ (n + 1 - i) * R i
      = (1 - α) * ∑ i ∈ Finset.Icc 1 n, α * (1 - α) ^ (n - i) * R i + α * R (n + 1) := by
  rw [Finset.sum_Icc_succ_top (by omega), Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_Icc] at hi
    rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
    ring
  · simp

theorem p093_weights (α : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, α * (1 - α) ^ (n - i) = 1 - (1 - α) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h := p093_sum_succ α (fun _ => 1) k
    simp only [mul_one] at h
    rw [h, ih]; ring

open SuttonBartoRL.Bandit in
theorem p093_main (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (Q R : ℕ → ℝ)
    (hQ : ∀ n : ℕ, 1 ≤ n → Q (n + 1) = Q n + unbiasedStepSize α n * (R n - Q n))
    (n : ℕ) (hn : 1 ≤ n) :
    traceOfOne α n * Q (n + 1) = ∑ i ∈ Finset.Icc 1 n, α * (1 - α) ^ (n - i) * R i := by
  induction n, hn using Nat.le_induction with
  | base =>
    have h1 := hQ 1 le_rfl
    have hpos := p093_trace_pos α hα0 hα1 1 le_rfl
    have ht : traceOfOne α 1 = α := by rw [p093_trace_eq]; ring
    rw [h1, unbiasedStepSize, ht, Finset.Icc_self, Finset.sum_singleton, div_self hα0.ne']
    simp
  | succ k hk ih =>
    have h1 := hQ (k + 1) (by omega)
    have hpos := p093_trace_pos α hα0 hα1 (k + 1) (by omega)
    rw [p093_sum_succ, ← ih, h1, unbiasedStepSize]
    have hrec : traceOfOne α (k + 1) = traceOfOne α k + α * (1 - traceOfOne α k) := rfl
    field_simp
    rw [hrec]
    ring

open SuttonBartoRL.Bandit in
theorem solution (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (Q R : ℕ → ℝ)
    (hQ : ∀ n : ℕ, 1 ≤ n → Q (n + 1) = Q n + unbiasedStepSize α n * (R n - Q n))
    (n : ℕ) (hn : 1 ≤ n) :
    Q (n + 1) = ∑ i ∈ Finset.Icc 1 n, (α * (1 - α) ^ (n - i) / traceOfOne α n) * R i ∧
      ∑ i ∈ Finset.Icc 1 n, α * (1 - α) ^ (n - i) / traceOfOne α n = 1 := by
  have hpos := p093_trace_pos α hα0 hα1 n hn
  have hm := p093_main α hα0 hα1 Q R hQ n hn
  constructor
  · have : ∑ i ∈ Finset.Icc 1 n, (α * (1 - α) ^ (n - i) / traceOfOne α n) * R i
        = (∑ i ∈ Finset.Icc 1 n, α * (1 - α) ^ (n - i) * R i) / traceOfOne α n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [this, ← hm]
    field_simp
  · rw [← Finset.sum_div, p093_weights, ← p093_trace_eq]
    exact div_self hpos.ne'
