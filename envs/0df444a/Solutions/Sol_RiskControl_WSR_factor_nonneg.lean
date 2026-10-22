-- Prove2me | solution 1 for RiskControl.WSR.factor_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:32:49.238108+00:00
-- url     : https://prove2.me/submissions/120e8d67-f603-469e-86b9-2f8e389e34ec

import Mathlib
import Definitions.Def_RiskControl_WSR_Process

set_option autoImplicit false
open MeasureTheory RiskControl.WSR

theorem nu_bounds (n : ℕ) (δ : ℝ) (ω : Fin n → ℝ) (i : ℕ) :
    0 ≤ nu n δ ω i ∧ nu n δ ω i ≤ 1 := by
  unfold nu
  exact ⟨le_min zero_le_one (Real.sqrt_nonneg _), min_le_left _ _⟩

theorem obs_mem (n : ℕ) (ω : Fin n → ℝ) (hω : ∀ j, ω j ∈ Set.Icc (0 : ℝ) 1) (j : ℕ) :
    obs ω j ∈ Set.Icc (0 : ℝ) 1 := by
  unfold obs
  split_ifs with h
  · exact hω _
  · simp

theorem solution (n : ℕ) (δ : ℝ) :
    (∀ (ω : Fin n → ℝ) (i : ℕ), 0 ≤ nu n δ ω i ∧ nu n δ ω i ≤ 1) ∧
    (∀ ω : Fin n → ℝ, (∀ j, ω j ∈ Set.Icc (0 : ℝ) 1) →
      ∀ R ∈ Set.Icc (0 : ℝ) 1, ∀ j : ℕ, 1 ≤ j → j ≤ n →
        0 ≤ 1 - nu n δ ω j * (obs ω j - R)) := by
  refine ⟨fun ω i => nu_bounds n δ ω i, ?_⟩
  intro ω hω R hR j _ _
  obtain ⟨h0, h1⟩ := nu_bounds n δ ω j
  obtain ⟨o0, o1⟩ := obs_mem n ω hω j
  obtain ⟨R0, R1⟩ := hR
  nlinarith [mul_nonneg h0 (sub_nonneg.2 (show obs ω j - R ≤ 1 by linarith)),
    mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (show obs ω j - R ≤ 1 by linarith))]
