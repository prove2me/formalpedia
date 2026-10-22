-- Prove2me | solution 1 for TwoSidedPD.Baseline.low_type_gain
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:40:29.021553+00:00
-- url     : https://prove2.me/submissions/3bb1051d-ad32-4377-925b-20fbae55359b

import Mathlib
import Definitions.Def_TwoSidedPD_Baseline_Setting
set_option autoImplicit false
open TwoSidedPD.Baseline MeasureTheory intervalIntegral

theorem BB_uden_pos (v b θH θL : ℝ) (hA : Assumption1 v b θH θL) : 0 < Uden b θH θL := by
  obtain ⟨⟨hv, hv2⟩, _⟩ := hA
  unfold Uden
  nlinarith [sq_nonneg (θH - θL)]

theorem BB_dden_pos (v b θH θL : ℝ) (hA : Assumption1 v b θH θL) : 0 < Dden b θH θL := by
  obtain ⟨⟨hv, hv2⟩, _⟩ := hA
  unfold Dden
  nlinarith

theorem BB_unif_opt (v b θH θL : ℝ) (hA : Assumption1 v b θH θL) (x : ℝ × ℝ) :
    IsUniformOpt v b θH θL x ↔
      (x.1 = 4 * v / Uden b θH θL ∧ x.2 = 2 * v * (2 * b + θH + θL) / Uden b θH θL) := by
  have hU := BB_uden_pos v b θH θL hA
  have hUdef : Uden b θH θL = 8 - 4 * (b + (θL + θH) / 2) ^ 2 := by unfold Uden; ring
  set m := b + (θL + θH) / 2 with hm
  have hf : ∀ a' c' : ℝ, profitU v b θH θL (a', c') = v * a' + m * a' * c' - a' ^ 2 - c' ^ 2 / 2 := by
    intro a' c'; simp only [profitU, PU, FU, hm]; ring
  have h2m : 2 * b + θH + θL = 2 * m := by rw [hm]; ring
  constructor
  · intro h
    obtain ⟨a, c⟩ := x
    have h1 := h (a + (v + m * c - 2 * a) / 2, c)
    have h2 := h (a, c + (m * a - c))
    rw [hf, hf] at h1 h2
    have g1 : v + m * c - 2 * a = 0 := by nlinarith [sq_nonneg (v + m * c - 2 * a)]
    have g2 : m * a - c = 0 := by nlinarith [sq_nonneg (m * a - c)]
    have hc : c = m * a := by linarith
    have ha : a * Uden b θH θL = 4 * v := by
      rw [hUdef]; rw [hc] at g1; nlinarith
    simp only
    rw [h2m]
    constructor
    · field_simp; linarith
    · rw [hc]; field_simp; linear_combination m * ha
  · rintro ⟨h1, h2⟩ x'
    obtain ⟨a', c'⟩ := x'
    obtain ⟨a, c⟩ := x
    simp only at h1 h2
    rw [hf, hf]
    rw [h2m] at h2
    have hmU : m ^ 2 < 2 := by rw [hUdef] at hU; linarith
    have g1 : v + m * c - 2 * a = 0 := by
      rw [h1, h2]; field_simp; rw [hUdef]; ring
    have g2 : m * a - c = 0 := by
      rw [h1, h2]; field_simp; ring
    have key : v * a' + m * a' * c' - a' ^ 2 - c' ^ 2 / 2 - (v * a + m * a * c - a ^ 2 - c ^ 2 / 2)
        = (v + m * c - 2 * a) * (a' - a) + (m * a - c) * (c' - c)
          - (a' - a) ^ 2 + m * (a' - a) * (c' - c) - (c' - c) ^ 2 / 2 := by ring
    have key2 : v * a' + m * a' * c' - a' ^ 2 - c' ^ 2 / 2 - (v * a + m * a * c - a ^ 2 - c ^ 2 / 2)
        = - (a' - a) ^ 2 + m * (a' - a) * (c' - c) - (c' - c) ^ 2 / 2 := by rw [key, g1, g2]; ring
    nlinarith [sq_nonneg ((c' - c) - m * (a' - a)), mul_nonneg (by linarith : (0:ℝ) ≤ 2 - m ^ 2) (sq_nonneg (a' - a))]

theorem BB_disc_opt (v b θH θL : ℝ) (hA : Assumption1 v b θH θL) (y : ℝ × ℝ × ℝ) :
    IsDiscrOpt v b θH θL y ↔
      (y.1 = 2 * v / Dden b θH θL ∧ y.2.1 = v * (b + θL) / Dden b θH θL ∧
        y.2.2 = v * (b + θH) / Dden b θH θL) := by
  have hD := BB_dden_pos v b θH θL hA
  have hDdef : Dden b θH θL = 4 - (b + θL) ^ 2 - (b + θH) ^ 2 := by unfold Dden; ring
  set p := b + θL with hp
  set q := b + θH with hq
  have hf : ∀ a' c' e' : ℝ, profitD v b θH θL (a', c', e') =
      v * a' + p * a' * c' + q * a' * e' - a' ^ 2 - c' ^ 2 - e' ^ 2 := by
    intro a' c' e'; simp only [profitD, PD, FDH, FDL, hp, hq]; ring
  constructor
  · intro h
    obtain ⟨a, c, e⟩ := y
    have h1 := h (a + (v + p * c + q * e - 2 * a) / 2, c, e)
    have h2 := h (a, c + (p * a - 2 * c) / 2, e)
    have h3 := h (a, c, e + (q * a - 2 * e) / 2)
    rw [hf, hf] at h1 h2 h3
    have g1 : v + p * c + q * e - 2 * a = 0 := by nlinarith [sq_nonneg (v + p * c + q * e - 2 * a)]
    have g2 : p * a - 2 * c = 0 := by nlinarith [sq_nonneg (p * a - 2 * c)]
    have g3 : q * a - 2 * e = 0 := by nlinarith [sq_nonneg (q * a - 2 * e)]
    have hc : c = p * a / 2 := by linarith
    have he : e = q * a / 2 := by linarith
    have ha : a * Dden b θH θL = 2 * v := by
      rw [hDdef]; rw [hc, he] at g1; nlinarith
    simp only
    refine ⟨?_, ?_, ?_⟩
    · field_simp; linarith
    · rw [hc]; field_simp; linear_combination p * ha
    · rw [he]; field_simp; linear_combination q * ha
  · rintro ⟨h1, h2, h3⟩ y'
    obtain ⟨a', c', e'⟩ := y'
    obtain ⟨a, c, e⟩ := y
    simp only at h1 h2 h3
    rw [hf, hf]
    have hpq : p ^ 2 + q ^ 2 < 4 := by rw [hDdef] at hD; linarith
    have g1 : v + p * c + q * e - 2 * a = 0 := by
      rw [h1, h2, h3]; field_simp; rw [hDdef]; ring
    have g2 : p * a - 2 * c = 0 := by
      rw [h1, h2]; field_simp; ring
    have g3 : q * a - 2 * e = 0 := by
      rw [h1, h3]; field_simp; ring
    have key : v * a' + p * a' * c' + q * a' * e' - a' ^ 2 - c' ^ 2 - e' ^ 2 -
        (v * a + p * a * c + q * a * e - a ^ 2 - c ^ 2 - e ^ 2)
        = (v + p * c + q * e - 2 * a) * (a' - a) + (p * a - 2 * c) * (c' - c) + (q * a - 2 * e) * (e' - e)
          - (a' - a) ^ 2 - (c' - c) ^ 2 - (e' - e) ^ 2 + p * (a' - a) * (c' - c) + q * (a' - a) * (e' - e) := by ring
    have key2 : v * a' + p * a' * c' + q * a' * e' - a' ^ 2 - c' ^ 2 - e' ^ 2 -
        (v * a + p * a * c + q * a * e - a ^ 2 - c ^ 2 - e ^ 2)
        = - (a' - a) ^ 2 - (c' - c) ^ 2 - (e' - e) ^ 2 + p * (a' - a) * (c' - c) + q * (a' - a) * (e' - e) := by
      rw [key, g1, g2, g3]; ring
    have e3 : - (a' - a) ^ 2 - (c' - c) ^ 2 - (e' - e) ^ 2 + p * (a' - a) * (c' - c) + q * (a' - a) * (e' - e)
        = - ((c' - c) - p * (a' - a) / 2) ^ 2 - ((e' - e) - q * (a' - a) / 2) ^ 2
          - ((4 - p ^ 2 - q ^ 2) / 4) * (a' - a) ^ 2 := by ring
    have n1 := sq_nonneg ((c' - c) - p * (a' - a) / 2)
    have n2 := sq_nonneg ((e' - e) - q * (a' - a) / 2)
    have n3 : 0 ≤ ((4 - p ^ 2 - q ^ 2) / 4) * (a' - a) ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith

theorem BB_int (A N : ℝ) : ∫ k in (0:ℝ)..N, (A - k) = A * N - N ^ 2 / 2 := by
  rw [intervalIntegral.integral_sub (by simp) (by simp)]
  simp [integral_id]
  ring

theorem BB_unif_vals (v b θH θL : ℝ) (hA : Assumption1 v b θH θL) (x : ℝ × ℝ)
    (hx : IsUniformOpt v b θH θL x) :
    x.1 = 4 * v / Uden b θH θL ∧ x.2 = 2 * v * (2 * b + θH + θL) / Uden b θH θL :=
  (BB_unif_opt v b θH θL hA x).1 hx

theorem BB_disc_vals (v b θH θL : ℝ) (hA : Assumption1 v b θH θL) (y : ℝ × ℝ × ℝ)
    (hy : IsDiscrOpt v b θH θL y) :
    y.1 = 2 * v / Dden b θH θL ∧ y.2.1 = v * (b + θL) / Dden b θH θL ∧
        y.2.2 = v * (b + θH) / Dden b θH θL :=
  (BB_disc_opt v b θH θL hA y).1 hy

theorem BB_dsur (v b θH θL : ℝ) (hA : Assumption1 v b θH θL) (y : ℝ × ℝ × ℝ)
    (hy : IsDiscrOpt v b θH θL y) :
      buyerSurplusD v b θH θL y = 2 * v ^ 2 / Dden b θH θL ^ 2 ∧
      sellerSurplusDH θH y = v ^ 2 * (b + θH) ^ 2 / (2 * Dden b θH θL ^ 2) ∧
      sellerSurplusDL θL y = v ^ 2 * (b + θL) ^ 2 / (2 * Dden b θH θL ^ 2) ∧
      welfareD v b θH θL y =
        v ^ 2 * (12 - 2 * b ^ 2 - θH ^ 2 - θL ^ 2 - 2 * b * (θH + θL)) / (2 * Dden b θH θL ^ 2) := by
  have hD := BB_dden_pos v b θH θL hA
  obtain ⟨h1, h2, h3⟩ := BB_disc_vals v b θH θL hA y hy
  have bs : buyerSurplusD v b θH θL y = 2 * v ^ 2 / Dden b θH θL ^ 2 := by
    unfold buyerSurplusD
    have : ∀ k : ℝ, v + b * (y.2.2 + y.2.1) - PD v b y.1 y.2.1 y.2.2 - k = (y.1 - k) := by
      intro k; simp only [PD]; ring
    simp_rw [this, BB_int]
    rw [h1]; field_simp; ring
  have sH : sellerSurplusDH θH y = v ^ 2 * (b + θH) ^ 2 / (2 * Dden b θH θL ^ 2) := by
    unfold sellerSurplusDH
    have : ∀ k : ℝ, θH * y.1 - FDH θH y.1 y.2.2 - k = (y.2.2 - k) := by
      intro k; simp only [FDH]; ring
    simp_rw [this, BB_int]
    rw [h3]; field_simp; ring
  have sL : sellerSurplusDL θL y = v ^ 2 * (b + θL) ^ 2 / (2 * Dden b θH θL ^ 2) := by
    unfold sellerSurplusDL
    have : ∀ k : ℝ, θL * y.1 - FDL θL y.1 y.2.1 - k = (y.2.1 - k) := by
      intro k; simp only [FDL]; ring
    simp_rw [this, BB_int]
    rw [h2]; field_simp; ring
  refine ⟨bs, sH, sL, ?_⟩
  unfold welfareD
  rw [bs, sH, sL]
  simp only [profitD, PD, FDH, FDL]; rw [h1, h2, h3]; field_simp; first | (unfold Dden; ring) | ring

theorem BB_usur (v b θH θL : ℝ) (hA : Assumption1 v b θH θL) :
    ∀ x : ℝ × ℝ, IsUniformOpt v b θH θL x →
      buyerSurplusU v b θH θL x = 8 * v ^ 2 / Uden b θH θL ^ 2 ∧
      sellerSurplusU θH θH θL x = v ^ 2 * (2 * b + 3 * θH - θL) ^ 2 / (2 * Uden b θH θL ^ 2) ∧
      sellerSurplusU θL θH θL x = v ^ 2 * (2 * b + 3 * θL - θH) ^ 2 / (2 * Uden b θH θL ^ 2) ∧
      welfareU v b θH θL x =
        v ^ 2 * (24 - (2 * b + 3 * θH - θL) * (2 * b - θH + 3 * θL)) / Uden b θH θL ^ 2 := by
  intro x hx
  have hU := BB_uden_pos v b θH θL hA
  obtain ⟨h1, h2⟩ := BB_unif_vals v b θH θL hA x hx
  have bs : buyerSurplusU v b θH θL x = 8 * v ^ 2 / Uden b θH θL ^ 2 := by
    unfold buyerSurplusU
    have : ∀ k : ℝ, v + b * (sellerU θH θH θL x + sellerU θL θH θL x) - PU v b x.1 x.2 - k =
        (x.1 - k) := by
      intro k; simp only [sellerU, PU, FU]; ring
    simp_rw [this, BB_int]
    rw [h1]; field_simp; ring
  have sH : sellerSurplusU θH θH θL x = v ^ 2 * (2 * b + 3 * θH - θL) ^ 2 / (2 * Uden b θH θL ^ 2) := by
    unfold sellerSurplusU
    have : ∀ k : ℝ, θH * x.1 - FU θH θL x.1 x.2 - k = (sellerU θH θH θL x - k) := by
      intro k; simp only [sellerU]
    simp_rw [this, BB_int]
    simp only [sellerU, FU]; rw [h1, h2]; field_simp; first | (unfold Uden; ring) | ring
  have sL : sellerSurplusU θL θH θL x = v ^ 2 * (2 * b + 3 * θL - θH) ^ 2 / (2 * Uden b θH θL ^ 2) := by
    unfold sellerSurplusU
    have : ∀ k : ℝ, θL * x.1 - FU θH θL x.1 x.2 - k = (sellerU θL θH θL x - k) := by
      intro k; simp only [sellerU]
    simp_rw [this, BB_int]
    simp only [sellerU, FU]; rw [h1, h2]; field_simp; first | (unfold Uden; ring) | ring
  refine ⟨bs, sH, sL, ?_⟩
  unfold welfareU
  rw [bs, sH, sL]
  simp only [profitU, PU, FU]; rw [h1, h2]; field_simp; first | (unfold Uden; ring) | ring

theorem solution (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    ∀ (x : ℝ × ℝ) (y : ℝ × ℝ × ℝ), IsUniformOpt v b θH θL x → IsDiscrOpt v b θH θL y →
      sellerSurplusDL θL y - sellerSurplusU θL θH θL x =
          1 / 2 * v ^ 2 * ((b + θL) ^ 2 / Dden b θH θL ^ 2 -
            (2 * b + 3 * θL - θH) ^ 2 / Uden b θH θL ^ 2) ∧
        sellerSurplusU θL θH θL x < sellerSurplusDL θL y := by
  intro x y hx hy
  have hU := BB_uden_pos v b θH θL hA
  have hD := BB_dden_pos v b θH θL hA
  obtain ⟨_, _, hsU, _⟩ := BB_usur v b θH θL hA x hx
  obtain ⟨_, _, hsD, _⟩ := BB_dsur v b θH θL hA y hy
  have hid : sellerSurplusDL θL y - sellerSurplusU θL θH θL x =
          1 / 2 * v ^ 2 * ((b + θL) ^ 2 / Dden b θH θL ^ 2 -
            (2 * b + 3 * θL - θH) ^ 2 / Uden b θH θL ^ 2) := by
    rw [hsU, hsD]; field_simp
  refine ⟨hid, ?_⟩
  obtain ⟨⟨hv, hv2⟩, hb2⟩ := hA
  have hw : 0 < 2 * b + 3 * θL - θH := by linarith
  have hp : 0 < b + θL := by linarith
  -- key polynomial inequality: (3p - q) D < p U
  have key : (2 * b + 3 * θL - θH) * Dden b θH θL < (b + θL) * Uden b θH θL := by
    have e : (b + θL) * Uden b θH θL - (2 * b + 3 * θL - θH) * Dden b θH θL
        = (θH - θL) * (4 - (2 * (b + θL) ^ 2 - (b + θL) * (b + θH) + (b + θH) ^ 2)) := by
      unfold Uden Dden; ring
    have h1 : 0 < θH - θL := by linarith
    have h2 : 0 < 4 - (2 * (b + θL) ^ 2 - (b + θL) * (b + θH) + (b + θH) ^ 2) := by
      nlinarith [mul_pos hp h1]
    nlinarith [mul_pos h1 h2]
  have hsq : (2 * b + 3 * θL - θH) ^ 2 / Uden b θH θL ^ 2 < (b + θL) ^ 2 / Dden b θH θL ^ 2 := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have h0 : 0 ≤ (2 * b + 3 * θL - θH) * Dden b θH θL := by positivity
    nlinarith [mul_self_lt_mul_self h0 key]
  have : 0 < sellerSurplusDL θL y - sellerSurplusU θL θH θL x := by
    rw [hid]
    have : 0 < v := hv
    have : 0 < (b + θL) ^ 2 / Dden b θH θL ^ 2 - (2 * b + 3 * θL - θH) ^ 2 / Uden b θH θL ^ 2 := by linarith
    positivity
  linarith
