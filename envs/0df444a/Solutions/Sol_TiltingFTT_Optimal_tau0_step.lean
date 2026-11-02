-- Prove2me | solution 1 for TiltingFTT.Optimal.tau0_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T06:49:09.642264+00:00
-- url     : https://prove2.me/submissions/da42d098-1c17-4760-917b-c17efd986922

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

open TiltingFTT.Optimal

set_option maxHeartbeats 1000000 in
theorem solution (P : Firm) (VH VL v : ℝ) (hS : Standing P) (h23 : Spec23 P VH VL v)
    (hv : 0 < v) :
    (∀ τ ∈ Set.Icc 0 (tauFB P), (poolWelfare P τ 1 < WS P τ ↔ τ < tau0 P v)) ∧
    (0 ≤ tau0 P v → tau0 P v ≤ tauFB P → WS P (tau0 P v) = poolWelfare P (tau0 P v) 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  obtain ⟨_, _, e1, e2, e3, e4, e5, e6⟩ := h23
  have hFL : 0 < P.FL := by linarith
  have hFH : 0 < P.FH := by linarith
  have hδI : 0 < P.δI := by linarith
  have hc : 0 < (1 - P.β) * (P.δI - P.δU) * P.FL := by
    have : 0 < 1 - P.β := by linarith
    have : 0 < P.δI - P.δU := by linarith
    positivity
  -- pooling welfare does not depend on τ
  have hpool : ∀ τ, poolWelfare P τ 1 = Wstar P - P.δI * v := by
    intro τ
    unfold poolWelfare welfare Wstar Fbar
    rw [e1, e2, e3, e4]; ring
  -- E > 0, Den = δU * E
  set E := (1 - P.β) * (P.δI - P.δU) * P.FL * (P.FH - P.FL) + P.δI * v * P.FL with hE
  have hEpos : 0 < E := by
    have := mul_pos hc (sub_pos.2 h7)
    have := mul_pos (mul_pos hδI hv) hFL
    linarith
  have hDen : 0 < P.δU * P.FL * ((1 - P.β) * (P.δI - P.δU) * (P.FH - P.FL) + P.δI * v) := by
    have : P.δU * P.FL * ((1 - P.β) * (P.δI - P.δU) * (P.FH - P.FL) + P.δI * v) = P.δU * E := by
      rw [hE]; ring
    rw [this]; exact mul_pos h10 hEpos
  set M := P.δI * ((1 - P.β) * (P.δI - P.δU) * P.FL) * (P.FH - P.FLH) + P.δI ^ 2 * v * P.FLH
    with hM
  clear_value E M
  -- τ < τ0 ↔ (1+τ) δU E < M (and same for equality)
  have htau0 : tau0 P v * (P.δU * P.FL * ((1 - P.β) * (P.δI - P.δU) * (P.FH - P.FL) + P.δI * v))
      = ((1 - P.β) * (P.δI - P.δU) * P.FL * (P.δI * (P.FH - P.FLH) - P.δU * (P.FH - P.FL)) +
      P.δI * (P.δI * P.FLH - P.δU * P.FL) * v) := by
    unfold tau0; exact div_mul_cancel₀ _ hDen.ne'
  -- core: for τ ≤ τFB, pool < WS ↔ (1+τ) δU E < M, and equality version
  have core : ∀ τ, (1 + τ) * P.δU ≤ P.δI →
      (poolWelfare P τ 1 < WS P τ ↔ (1 + τ) * P.δU * E < M) ∧
      ((1 + τ) * P.δU * E = M → WS P τ = poolWelfare P τ 1) := by
    intro τ hk
    have hD : 0 < P.δI * P.FLH - (1 + τ) * P.δU * P.FL := by
      nlinarith [mul_le_mul_of_nonneg_right hk hFL.le, mul_lt_mul_of_pos_left h5 hδI]
    have htD : Tbar P τ * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL) =
        (P.δI - (1 + τ) * P.δU) * P.FH := by
      unfold Tbar; exact div_mul_cancel₀ _ hD.ne'
    have hX : (1 - P.β) * (P.δI - P.δU) * (1 - Tbar P τ) * P.FL *
        (P.δI * P.FLH - (1 + τ) * P.δU * P.FL) =
        (1 - P.β) * (P.δI - P.δU) * P.FL * ((P.δI * P.FLH - (1 + τ) * P.δU * P.FL) -
          (P.δI - (1 + τ) * P.δU) * P.FH) := by
      rw [← htD]; ring
    have hid : (1 - P.β) * (P.δI - P.δU) * P.FL * ((P.δI * P.FLH - (1 + τ) * P.δU * P.FL) -
          (P.δI - (1 + τ) * P.δU) * P.FH) - P.δI * v * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL)
        = (1 + τ) * P.δU * E - M := by
      rw [hE, hM]; ring
    rw [hpool τ]
    unfold WS
    constructor
    · constructor
      · intro h
        have h' : (1 - P.β) * (P.δI - P.δU) * (1 - Tbar P τ) * P.FL < P.δI * v := by linarith
        have := mul_lt_mul_of_pos_right h' hD
        linarith
      · intro h
        by_contra hc'
        rw [not_lt] at hc'
        have h' : P.δI * v ≤ (1 - P.β) * (P.δI - P.δU) * (1 - Tbar P τ) * P.FL := by linarith
        have := mul_le_mul_of_nonneg_right h' hD.le
        linarith
    · intro h
      have h' : (1 - P.β) * (P.δI - P.δU) * (1 - Tbar P τ) * P.FL *
          (P.δI * P.FLH - (1 + τ) * P.δU * P.FL) =
          P.δI * v * (P.δI * P.FLH - (1 + τ) * P.δU * P.FL) := by linarith
      have := mul_right_cancel₀ hD.ne' h'
      linarith
  have hkFB : ∀ τ, τ ≤ tauFB P → (1 + τ) * P.δU ≤ P.δI := by
    intro τ h
    unfold tauFB at h
    have : 1 + τ ≤ P.δI / P.δU := by linarith
    rwa [le_div_iff₀ h10] at this
  have hlin : tau0 P v * (P.δU * E) = M - P.δU * E := by
    have : P.δU * P.FL * ((1 - P.β) * (P.δI - P.δU) * (P.FH - P.FL) + P.δI * v) = P.δU * E := by
      rw [hE]; ring
    rw [← this, htau0, hM]; ring
  have hDE : 0 < P.δU * E := mul_pos h10 hEpos
  constructor
  · intro τ hτ
    rw [(core τ (hkFB τ hτ.2)).1]
    constructor
    · intro h
        -- (1+τ) δU E < M = (1 + τ0) δU E
      by_contra hc'
      rw [not_lt] at hc'
      have := mul_le_mul_of_nonneg_right hc' hDE.le
      linarith
    · intro h
      have := mul_lt_mul_of_pos_right h hDE
      linarith
  · intro _ hτ
    apply (core _ (hkFB _ hτ)).2
    linear_combination hlin
