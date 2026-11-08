-- Prove2me | solution 1 for ParallelServerStab.overflow_iff
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T00:18:55.774191+00:00
-- url     : https://prove2.me/submissions/41d00e2a-deab-46cd-85ec-1822971e2d51

import Mathlib
import Definitions.Def_ParallelServerStab_Vcr
import Definitions.Def_ParallelServerStab_piF

open ParallelServerStab in
theorem solution (s : ℕ) (hs : 2 ≤ s) (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) (lam μ : ℝ)
    (hlam : 0 < lam) (hμ : 0 < μ) :
    Vcr s p < lam / (s * μ) ↔ ((s : ℝ) - 1) * μ < lam * p * (1 - piF lam μ p 0) := by
  have hS : (2 : ℝ) ≤ s := by exact_mod_cast hs
  set c : ℝ := (s : ℝ) - 1 with hc
  have hc1 : 1 ≤ c := by rw [hc]; linarith
  have hpc : 0 < p * c := by positivity
  set q : ℝ := Real.sqrt (1 + 4 / (p * c)) with hq
  have hq2 : q ^ 2 = 1 + 4 / (p * c) := Real.sq_sqrt (by positivity)
  have hq2' : p * c * q ^ 2 = p * c + 4 := by rw [hq2]; field_simp
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have h4 : 0 < 4 / (p * c) := by positivity
  have hq1sq : (1 : ℝ) ≤ q ^ 2 := by rw [hq2]; linarith
  have hq1 : 1 ≤ q := by nlinarith
  -- left-hand side
  have hL : Vcr s p < lam / (s * μ) ↔ c * (1 + q) * μ < 2 * lam := by
    unfold Vcr
    rw [← hc, ← hq]
    have hSpos : (0 : ℝ) < s := by linarith
    rw [show c / (2 * (s : ℝ)) * (1 + q) = (c * (1 + q)) / (2 * s) by ring,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  -- right-hand side
  have hpi : 1 - piF lam μ p 0 = lam / (μ + lam * p) := by
    unfold piF
    rw [if_pos rfl]
    field_simp <;> ring
  have hR : c * μ < lam * p * (1 - piF lam μ p 0) ↔ c * μ * (μ + lam * p) < p * lam ^ 2 := by
    rw [hpi, show lam * p * (lam / (μ + lam * p)) = p * lam ^ 2 / (μ + lam * p) by ring,
      lt_div_iff₀ (by positivity)]
  rw [hL, hR]
  set A := 2 * lam - c * (1 + q) * μ with hA
  set B := 2 * lam - c * (1 - q) * μ with hB
  have hBpos : 0 < B := by
    rw [hB]
    have : 0 ≤ c * (q - 1) * μ := by
      have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ c) (by linarith : (0:ℝ) ≤ q - 1)) hμ.le
      exact this
    nlinarith
  have hid : p * lam ^ 2 - c * μ * (μ + lam * p) = p / 4 * A * B := by
    rw [hA, hB]
    linear_combination (c * μ ^ 2 / 4) * hq2'
  constructor
  · intro h
    have hApos : 0 < A := by rw [hA]; linarith
    have : 0 < p / 4 * A * B := by positivity
    linarith
  · intro h
    by_contra hneg
    have hA0 : A ≤ 0 := by rw [hA]; linarith
    have : p / 4 * A * B ≤ 0 := by
      have h1 : p / 4 * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hA0
      exact mul_nonpos_of_nonpos_of_nonneg h1 hBpos.le
    linarith
