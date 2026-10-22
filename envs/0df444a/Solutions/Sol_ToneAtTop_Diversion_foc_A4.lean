-- Prove2me | solution 1 for ToneAtTop.Diversion.foc_A4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:38:20.732002+00:00
-- url     : https://prove2.me/submissions/9049d3d0-eabc-47c6-887b-a83b05df3462

import Mathlib
import Definitions.Def_ToneAtTop_Diversion_Model
set_option autoImplicit false

theorem solution (P : ToneAtTop.Diversion.Params) (hS : P.Standing)
    (hk : 0 < 2 * P.lam * P.xbar - P.p * P.tau ^ 2) :
    ∀ c ∈ Set.Ico (0 : ℝ) (1 - P.tau / P.xbar),
      HasDerivAt
        (fun u : ℝ =>
          (2 * P.lam * P.xbar + (1 - u) ^ 2 * P.xbar ^ 2 - P.p * P.tau ^ 2) /
            (2 * (1 - u) * P.xbar))
        0 c ↔
      c = 1 - Real.sqrt (2 * P.lam * P.xbar - P.p * P.tau ^ 2) / P.xbar := by
  intro c hc
  obtain ⟨hx, hl, hp0, hp1, hβ, hγ0, hγ1, hη, hτ⟩ := hS
  have htau : 0 < P.tau := by
    unfold ToneAtTop.Diversion.Params.tau
    have : 0 < 1 - P.β := by linarith
    positivity
  set K : ℝ := 2 * P.lam * P.xbar - P.p * P.tau ^ 2 with hKdef
  have hw : 0 < 1 - c := by
    have h1 : P.tau / P.xbar < 1 - c := by linarith [hc.2]
    have h2 : 0 < P.tau / P.xbar := by positivity
    linarith
  have hu : HasDerivAt (fun u : ℝ => 1 - u) (-1) c := (hasDerivAt_id' c).const_sub 1
  have hnum : HasDerivAt (fun u : ℝ => 2 * P.lam * P.xbar + (1 - u) ^ 2 * P.xbar ^ 2 - P.p * P.tau ^ 2)
      (↑2 * (1 - c) ^ (2 - 1) * (-1) * P.xbar ^ 2) c := by
    have := (((hu.pow 2).mul_const (P.xbar ^ 2)).const_add (2 * P.lam * P.xbar)).sub_const (P.p * P.tau ^ 2)
    exact this
  have hden : HasDerivAt (fun u : ℝ => 2 * (1 - u) * P.xbar) (2 * (-1) * P.xbar) c := by
    exact (hu.const_mul 2).mul_const P.xbar
  have hne : 2 * (1 - c) * P.xbar ≠ 0 := by positivity
  have hd := hnum.div hden hne
  have hd' : HasDerivAt
        (fun u : ℝ =>
          (2 * P.lam * P.xbar + (1 - u) ^ 2 * P.xbar ^ 2 - P.p * P.tau ^ 2) /
            (2 * (1 - u) * P.xbar))
        ((K - (1 - c) ^ 2 * P.xbar ^ 2) / (2 * (1 - c) ^ 2 * P.xbar)) c := by
    refine hd.congr_deriv ?_
    simp only [hKdef, Nat.cast_ofNat]
    field_simp
    ring
  constructor
  · intro h
    have h0 := h.unique hd'
    have h1 : K - (1 - c) ^ 2 * P.xbar ^ 2 = 0 := by
      have hpos : 0 < 2 * (1 - c) ^ 2 * P.xbar := by positivity
      have := h0.symm
      rw [div_eq_zero_iff] at this
      rcases this with h | h
      · exact h
      · exact absurd h (ne_of_gt hpos)
    have h2 : ((1 - c) * P.xbar) ^ 2 = K := by nlinarith
    have h3 : (1 - c) * P.xbar = Real.sqrt K := by
      rw [← h2, Real.sqrt_sq (by positivity)]
    have h4 : 1 - c = Real.sqrt K / P.xbar := by
      rw [← h3]; field_simp
    linarith
  · intro h
    have h3 : (1 - c) * P.xbar = Real.sqrt K := by
      have : 1 - c = Real.sqrt K / P.xbar := by linarith
      rw [this]; field_simp
    have h2 : ((1 - c) * P.xbar) ^ 2 = K := by
      rw [h3, Real.sq_sqrt hk.le]
    have h1 : K - (1 - c) ^ 2 * P.xbar ^ 2 = 0 := by nlinarith
    rw [h1, zero_div] at hd'
    exact hd'
