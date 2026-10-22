-- Prove2me | solution 1 for RiskControl.WSR.K_monotone
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:33:44.63135+00:00
-- url     : https://prove2.me/submissions/4a53dace-8d97-411b-9727-34b2f3220de0

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

theorem K_mono (n : ℕ) (δ : ℝ) (ω : Fin n → ℝ) (hω : ∀ j, ω j ∈ Set.Icc (0 : ℝ) 1)
    (i : ℕ) : MonotoneOn (fun R => K n δ ω i R) (Set.Ici 0) := by
  intro R hR S hS hRS
  simp only [Set.mem_Ici] at hR hS
  unfold K
  apply Finset.prod_le_prod
  · intro j _
    obtain ⟨h0, h1⟩ := nu_bounds n δ ω j
    obtain ⟨o0, o1⟩ := obs_mem n ω hω j
    nlinarith [mul_nonneg h0 (sub_nonneg.2 (show obs ω j - R ≤ 1 by linarith))]
  · intro j _
    obtain ⟨h0, h1⟩ := nu_bounds n δ ω j
    nlinarith [mul_nonneg h0 (sub_nonneg.2 hRS)]

theorem solution (n : ℕ) (δ : ℝ) (ω : Fin n → ℝ) (hω : ∀ j, ω j ∈ Set.Icc (0 : ℝ) 1)
    (i : ℕ) :
    MonotoneOn (fun R => K n δ ω i R) (Set.Ici 0) := K_mono n δ ω hω i
