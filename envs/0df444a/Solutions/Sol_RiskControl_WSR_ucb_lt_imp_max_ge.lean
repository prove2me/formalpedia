-- Prove2me | solution 1 for RiskControl.WSR.ucb_lt_imp_max_ge
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:35:23.786658+00:00
-- url     : https://prove2.me/submissions/0d152b2d-f330-4aec-afa5-eb475d4fe0d4

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

theorem solution (n : ℕ) (δ : ℝ) (ω : Fin n → ℝ)
    (hω : ∀ j, ω j ∈ Set.Icc (0 : ℝ) 1) (R : ℝ) (hR : 0 ≤ R) :
    wsrUCB n δ ω < (R : EReal) → ∃ i ∈ Finset.Icc 1 n, 1 / δ ≤ K n δ ω i R := by
  intro h
  unfold wsrUCB at h
  rw [sInf_lt_iff] at h
  obtain ⟨a, ⟨R', ⟨hR'0, i, hi, hK⟩, rfl⟩, hlt⟩ := h
  have hlt' : R' < R := EReal.coe_lt_coe_iff.1 hlt
  exact ⟨i, hi, hK.le.trans (K_mono n δ ω hω i (Set.mem_Ici.2 hR'0) (Set.mem_Ici.2 hR) hlt'.le)⟩
