-- Prove2me | solution 1 for TwoSidedPD.Baseline.uniform_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:30:32.11702+00:00
-- url     : https://prove2.me/submissions/40f08e8f-780c-4b3d-a7b5-22038fa4e3d4

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
theorem solution (v b θH θL : ℝ) (hL : 0 < θL) (hLH : θL < θH) (hb : 0 < b)
    (hA : Assumption1 v b θH θL) :
    (∃ x : ℝ × ℝ, IsUniformOpt v b θH θL x) ∧
    ∀ x : ℝ × ℝ, IsUniformOpt v b θH θL x →
      x.2 = 2 * v * (2 * b + θH + θL) / Uden b θH θL ∧
      x.1 = 4 * v / Uden b θH θL ∧
      PU v b x.1 x.2 = v * (4 - (θH + θL) * (2 * b + θH + θL)) / Uden b θH θL ∧
      FU θH θL x.1 x.2 = v * (θH + θL - 2 * b) / Uden b θH θL ∧
      profitU v b θH θL x = 2 * v ^ 2 / Uden b θH θL ∧
      sellerU θH θH θL x = v * (2 * b + 3 * θH - θL) / Uden b θH θL ∧
      sellerU θL θH θL x = v * (2 * b + 3 * θL - θH) / Uden b θH θL := by
  have hU := BB_uden_pos v b θH θL hA
  refine ⟨⟨(4 * v / Uden b θH θL, 2 * v * (2 * b + θH + θL) / Uden b θH θL),
    (BB_unif_opt v b θH θL hA _).2 ⟨rfl, rfl⟩⟩, ?_⟩
  intro x hx
  obtain ⟨h1, h2⟩ := (BB_unif_opt v b θH θL hA x).1 hx
  refine ⟨h2, h1, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [PU]; rw [h1, h2]; field_simp; first | (unfold Uden; ring) | ring
  · simp only [FU]; rw [h1, h2]; field_simp; first | (unfold Uden; ring) | ring
  · simp only [profitU, PU, FU]; rw [h1, h2]; field_simp; first | (unfold Uden; ring) | ring
  · simp only [sellerU, FU]; rw [h1, h2]; field_simp; first | (unfold Uden; ring) | ring
  · simp only [sellerU, FU]; rw [h1, h2]; field_simp; first | (unfold Uden; ring) | ring
