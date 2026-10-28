-- Prove2me | solution 1 for TiltingFTT.Optimal.tbar_deriv
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:27:20.917569+00:00
-- url     : https://prove2.me/submissions/f2038608-2cd9-4153-bae5-a75543ea3133

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

open TiltingFTT.Optimal in
theorem solution (P : Firm) (hS : Standing P) :
    (∀ τ, 0 ≤ τ → Cond15 P τ →
      HasDerivAt (Tbar P)
        (P.δI * P.δU * P.FH * (P.FL - P.FLH) / (P.δI * P.FLH - P.δU * P.FL * (1 + τ)) ^ 2) τ ∧
      P.δI * P.δU * P.FH * (P.FL - P.FLH) / (P.δI * P.FLH - P.δU * P.FL * (1 + τ)) ^ 2 < 0) ∧
    StrictAntiOn (Tbar P) (Set.Icc 0 (tauFB P)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := hS
  have hFL : 0 < P.FL := by linarith
  have hFH : 0 < P.FH := by linarith
  have hδI : 0 < P.δI := by linarith
  have hD : ∀ τ : ℝ, (1 + τ) * P.δU ≤ P.δI → 0 < P.δI * P.FLH - (1 + τ) * P.δU * P.FL := by
    intro τ h
    have a := mul_le_mul_of_nonneg_right h hFL.le
    have b := mul_lt_mul_of_pos_left h5 hδI
    linarith
  have hT : Tbar P = fun τ => (P.δI - (1 + τ) * P.δU) * P.FH /
      (P.δI * P.FLH - (1 + τ) * P.δU * P.FL) := rfl
  have hder : ∀ τ : ℝ, (1 + τ) * P.δU ≤ P.δI →
      HasDerivAt (Tbar P)
        (P.δI * P.δU * P.FH * (P.FL - P.FLH) / (P.δI * P.FLH - P.δU * P.FL * (1 + τ)) ^ 2) τ := by
    intro τ h
    have hd := hD τ h
    have hN : HasDerivAt (fun τ : ℝ => (P.δI - (1 + τ) * P.δU) * P.FH) (-(1 * P.δU) * P.FH) τ :=
      ((((hasDerivAt_id τ).const_add 1).mul_const P.δU).const_sub P.δI).mul_const P.FH
    have hDd : HasDerivAt (fun τ : ℝ => P.δI * P.FLH - (1 + τ) * P.δU * P.FL)
        (-(1 * P.δU * P.FL)) τ :=
      ((((hasDerivAt_id τ).const_add 1).mul_const P.δU).mul_const P.FL).const_sub _
    rw [hT]
    refine (hN.div hDd hd.ne').congr_deriv ?_
    have e : P.δI * P.FLH - P.δU * P.FL * (1 + τ) = P.δI * P.FLH - (1 + τ) * P.δU * P.FL := by ring
    rw [e]
    field_simp
    ring
  have hneg : ∀ τ : ℝ, (1 + τ) * P.δU ≤ P.δI →
      P.δI * P.δU * P.FH * (P.FL - P.FLH) / (P.δI * P.FLH - P.δU * P.FL * (1 + τ)) ^ 2 < 0 := by
    intro τ h
    have hd := hD τ h
    apply div_neg_of_neg_of_pos
    · have : 0 < P.δI * P.δU * P.FH := by positivity
      nlinarith
    · have e : P.δI * P.FLH - P.δU * P.FL * (1 + τ) = P.δI * P.FLH - (1 + τ) * P.δU * P.FL := by ring
      rw [e]
      positivity
  have hc15 : ∀ x ∈ Set.Icc 0 (tauFB P), (1 + x) * P.δU ≤ P.δI := by
    intro x hx
    have := hx.2
    unfold tauFB at this
    have : 1 + x ≤ P.δI / P.δU := by linarith
    rwa [le_div_iff₀ h10] at this
  refine ⟨fun τ _ h => ⟨hder τ h, hneg τ h⟩, ?_⟩
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _)
  · intro x hx
    exact (hder x (hc15 x hx)).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : x ∈ Set.Icc 0 (tauFB P) := interior_subset hx
    rw [(hder x (hc15 x hx')).deriv]
    exact hneg x (hc15 x hx')
