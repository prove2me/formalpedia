-- Prove2me | solution 1 for Shoppertainment.OptimalBandwidth.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:42:25.6442+00:00
-- url     : https://prove2.me/submissions/35831e31-f92c-4a78-90fa-52f99ba613a0

import Mathlib
import Definitions.Def_Shoppertainment_OptimalBandwidth_Model

set_option autoImplicit false
open Shoppertainment.OptimalBandwidth

theorem solution (α v te q T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hv : 0 < v) (hT : 0 < T)
    (hq : 0 < q) (hq1 : q ≤ 1) (hte : te ∈ Set.Icc (0:ℝ) 1) :
    (1 / (2 - q) < te → 0 < pL v te q ∧ ∀ p : ℝ, 0 < p → p ≠ pL v te q →
        mfrProfit α v te q T p < mfrProfit α v te q T (pL v te q)) ∧
    (te ≤ 1 / (2 - q) → 0 < pH v te q ∧ ∀ p : ℝ, 0 < p →
        mfrProfit α v te q T p ≤ mfrProfit α v te q T (pH v te q)) := by
  obtain ⟨hte0, hte1⟩ := hte
  have h2q : 0 < 2 - q := by linarith
  have hc : 0 < 1 - α := by linarith
  have hqv : 0 < q * v := mul_pos hq hv
  have hLH : pL v te q = te * (q * v) := by unfold pL; ring
  have hHm : pH v te q = (1 - te + te * q) * v := rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [div_lt_iff₀ h2q] at h
    have hte' : 0 < te := by nlinarith
    have hpL : 0 < pL v te q := by rw [hLH]; exact mul_pos hte' hqv
    refine ⟨hpL, fun p hp hne => ?_⟩
    have hHq : pH v te q * q < pL v te q := by
      rw [hLH, hHm]; nlinarith [mul_pos hqv hv]
    have hdL : demand v te q T (pL v te q) = T := by unfold demand; simp
    unfold mfrProfit
    rw [hdL]
    unfold demand
    by_cases h1 : p ≤ pL v te q
    · rw [if_pos h1]
      have : p < pL v te q := lt_of_le_of_ne h1 hne
      have : (1 - α) * p * T < (1 - α) * pL v te q * T := by
        have := mul_pos hc hT
        nlinarith
      exact this
    · rw [if_neg h1]
      by_cases h2 : p ≤ pH v te q
      · rw [if_pos h2]
        have h3 : p * q ≤ pH v te q * q := mul_le_mul_of_nonneg_right h2 hq.le
        have := mul_pos hc hT
        nlinarith
      · rw [if_neg h2]
        have := mul_pos (mul_pos hc hpL) hT
        nlinarith
  · rw [le_div_iff₀ h2q] at h
    have hH : 0 < pH v te q := by
      rw [hHm]
      apply mul_pos _ hv
      rcases hte0.eq_or_lt with h0 | h0
      · rw [← h0]; norm_num
      · nlinarith [mul_pos h0 hq]
    refine ⟨hH, fun p hp => ?_⟩
    have hLq : pL v te q ≤ pH v te q * q := by
      rw [hLH, hHm]; nlinarith [mul_pos hqv hv, mul_pos hq hv]
    have hdH : demand v te q T (pH v te q) = q * T := by
      unfold demand
      by_cases h1 : pH v te q ≤ pL v te q
      · rw [if_pos h1]
        have : te = 1 := by
          rw [hLH, hHm] at h1
          nlinarith [mul_pos hq hv]
        subst this
        have hq' : q = 1 := by nlinarith
        subst hq'
        ring
      · rw [if_neg h1, if_pos le_rfl]
    unfold mfrProfit
    rw [hdH]
    unfold demand
    by_cases h1 : p ≤ pL v te q
    · rw [if_pos h1]
      have h3 : p * T ≤ pH v te q * q * T := by
        have : p ≤ pH v te q * q := h1.trans hLq
        exact mul_le_mul_of_nonneg_right this hT.le
      nlinarith
    · rw [if_neg h1]
      by_cases h2 : p ≤ pH v te q
      · rw [if_pos h2]
        have h3 : p * q ≤ pH v te q * q := mul_le_mul_of_nonneg_right h2 hq.le
        have := mul_pos hc hT
        nlinarith
      · rw [if_neg h2]
        have := mul_pos (mul_pos hc hH) (mul_pos hq hT)
        nlinarith
