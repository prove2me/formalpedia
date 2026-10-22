-- Prove2me | solution 1 for TwoSidedPD.Baseline.high_type_gain_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:39:51.254439+00:00
-- url     : https://prove2.me/submissions/889810f1-7b0e-4b21-b48e-46fb417e0c6a

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting

set_option autoImplicit false

open TwoSidedPD.Baseline

theorem int_lin_aux (a N : ℝ) : ∫ k in (0:ℝ)..N, (a - k) = a * N - N ^ 2 / 2 := by
  rw [intervalIntegral.integral_sub (by simp) (by simp)]
  simp
  ring

theorem solution (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    ∀ (x : ℝ × ℝ) (y : ℝ × ℝ × ℝ), IsUniformOpt v b θH θL x → IsDiscrOpt v b θH θL y →
      sellerSurplusDH θH y - sellerSurplusU θH θH θL x =
          1 / 2 * v ^ 2 * ((b + θH) ^ 2 / Dden b θH θL ^ 2 -
            (2 * b + 3 * θH - θL) ^ 2 / Uden b θH θL ^ 2) ∧
        (sellerSurplusU θH θH θL x < sellerSurplusDH θH y ↔ bhat θH θL < b) := by
  intro x y hx hy
  obtain ⟨⟨hv0, hv1⟩, _⟩ := hA
  have hD : 0 < Dden b θH θL := by unfold Dden; nlinarith
  have hU : 0 < Uden b θH θL := by
    unfold Uden; unfold Dden at hD
    nlinarith [sq_nonneg (θH - θL)]
  -- first order conditions, uniform pricing
  obtain ⟨NB, NS⟩ := x
  have hgB : v + (b + (θL + θH) / 2) * NS - 2 * NB = 0 := by
    have h := hx (NB + (v + (b + (θL + θH) / 2) * NS - 2 * NB) / 2, NS)
    simp only [profitU, PU, FU] at h
    have : (v + (b + (θL + θH) / 2) * NS - 2 * NB) ^ 2 ≤ 0 := by nlinarith [h]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
  have hgS : (b + (θL + θH) / 2) * NB - NS = 0 := by
    have h := hx (NB, NS + ((b + (θL + θH) / 2) * NB - NS) / 2)
    simp only [profitU, PU, FU] at h
    have : ((b + (θL + θH) / 2) * NB - NS) ^ 2 ≤ 0 := by nlinarith [h]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
  obtain ⟨MB, ML, MH⟩ := y
  have hdB : v + (b + θL) * ML + (b + θH) * MH - 2 * MB = 0 := by
    have h := hy (MB + (v + (b + θL) * ML + (b + θH) * MH - 2 * MB) / 2, ML, MH)
    simp only [profitD, PD, FDL, FDH] at h
    have : (v + (b + θL) * ML + (b + θH) * MH - 2 * MB) ^ 2 ≤ 0 := by nlinarith [h]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
  have hdL : (b + θL) * MB - 2 * ML = 0 := by
    have h := hy (MB, ML + ((b + θL) * MB - 2 * ML) / 2, MH)
    simp only [profitD, PD, FDL, FDH] at h
    have : ((b + θL) * MB - 2 * ML) ^ 2 ≤ 0 := by nlinarith [h]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
  have hdH : (b + θH) * MB - 2 * MH = 0 := by
    have h := hy (MB, ML, MH + ((b + θH) * MB - 2 * MH) / 2)
    simp only [profitD, PD, FDL, FDH] at h
    have : ((b + θH) * MB - 2 * MH) ^ 2 ≤ 0 := by nlinarith [h]
    exact pow_eq_zero_iff (two_ne_zero) |>.mp (le_antisymm this (sq_nonneg _))
  -- solve
  have hUne : Uden b θH θL ≠ 0 := hU.ne'
  have hDne : Dden b θH θL ≠ 0 := hD.ne'
  have hNB : NB = 4 * v / Uden b θH θL := by
    rw [eq_div_iff hUne]; unfold Uden
    have : NS = (b + (θL + θH) / 2) * NB := by linarith
    rw [this] at hgB
    nlinarith [hgB]
  have hNS : NS = (b + (θL + θH) / 2) * NB := by linarith
  have hMB : MB = 2 * v / Dden b θH θL := by
    rw [eq_div_iff hDne]; unfold Dden
    have e1 : ML = (b + θL) * MB / 2 := by linarith
    have e2 : MH = (b + θH) * MB / 2 := by linarith
    rw [e1, e2] at hdB
    nlinarith [hdB]
  have hMH : MH = (b + θH) * v / Dden b θH θL := by
    have e2 : MH = (b + θH) * MB / 2 := by linarith
    rw [e2, hMB]; field_simp
  -- integrals
  have hSU : sellerSurplusU θH θH θL (NB, NS) = (θH * NB - FU θH θL NB NS) ^ 2 / 2 := by
    unfold sellerSurplusU sellerU
    rw [int_lin_aux]; ring
  have hSD : sellerSurplusDH θH (MB, ML, MH) = MH ^ 2 / 2 := by
    unfold sellerSurplusDH FDH
    simp only
    rw [show (fun k : ℝ => θH * MB - (θH * MB - MH) - k) = fun k => MH - k by ext k; ring]
    rw [int_lin_aux]; ring
  have hN : θH * NB - FU θH θL NB NS = v * (2 * b + 3 * θH - θL) / Uden b θH θL := by
    unfold FU
    rw [hNS, hNB]; unfold Uden; field_simp; ring
  have key : sellerSurplusDH θH (MB, ML, MH) - sellerSurplusU θH θH θL (NB, NS) =
      1 / 2 * v ^ 2 * ((b + θH) ^ 2 / Dden b θH θL ^ 2 -
            (2 * b + 3 * θH - θL) ^ 2 / Uden b θH θL ^ 2) := by
    rw [hSD, hSU, hN, hMH]; field_simp
  refine ⟨key, ?_⟩
  -- sign analysis
  have hp1 : 0 < b + θH := by linarith
  have hp2 : 0 < 2 * b + 3 * θH - θL := by linarith
  have hfac : (b + θH) * Uden b θH θL - (2 * b + 3 * θH - θL) * Dden b θH θL
      = (θH - θL) * (2 * θH ^ 2 - θH * θL + 3 * θH * b + θL ^ 2 + θL * b + 2 * b ^ 2 - 4) := by
    unfold Uden Dden; ring
  have hX : sellerSurplusU θH θH θL (NB, NS) < sellerSurplusDH θH (MB, ML, MH) ↔
      0 < (b + θH) * Uden b θH θL - (2 * b + 3 * θH - θL) * Dden b θH θL := by
    rw [← sub_pos, key]
    have hv2 : 0 < 1 / 2 * v ^ 2 := by positivity
    rw [mul_pos_iff_of_pos_left hv2]
    have : (b + θH) ^ 2 / Dden b θH θL ^ 2 - (2 * b + 3 * θH - θL) ^ 2 / Uden b θH θL ^ 2
        = (((b + θH) * Uden b θH θL) ^ 2 - ((2 * b + 3 * θH - θL) * Dden b θH θL) ^ 2)
          / (Dden b θH θL ^ 2 * Uden b θH θL ^ 2) := by
      field_simp
    rw [this, div_pos_iff_of_pos_right (by positivity)]
    have hA' : 0 < (b + θH) * Uden b θH θL := mul_pos hp1 hU
    have hB' : 0 < (2 * b + 3 * θH - θL) * Dden b θH θL := mul_pos hp2 hD
    rw [sub_pos, sub_pos]
    exact sq_lt_sq₀ hB'.le hA'.le
  rw [hX, hfac]
  have hLH' : 0 < θH - θL := by linarith
  rw [mul_pos_iff_of_pos_left hLH']
  unfold bhat
  have hm : 0 < 4 * b + 3 * θH + θL := by linarith
  have : (Real.sqrt (32 - 7 * (θH - θL) ^ 2) - 3 * θH - θL) / 4 < b ↔
      Real.sqrt (32 - 7 * (θH - θL) ^ 2) < 4 * b + 3 * θH + θL := by
    constructor <;> intro h <;> linarith
  rw [this, Real.sqrt_lt' hm]
  have e : (4 * b + 3 * θH + θL) ^ 2 - (32 - 7 * (θH - θL) ^ 2)
      = 8 * (2 * θH ^ 2 - θH * θL + 3 * θH * b + θL ^ 2 + θL * b + 2 * b ^ 2 - 4) := by ring
  constructor <;> intro h <;> linarith
