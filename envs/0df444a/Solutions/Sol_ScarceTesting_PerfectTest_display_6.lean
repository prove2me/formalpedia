-- Prove2me | solution 1 for ScarceTesting.PerfectTest.display_6
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:02:15.235376+00:00
-- url     : https://prove2.me/submissions/14429cd7-ff9f-424f-8311-2c1b1b487ff4

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting

set_option autoImplicit false
open MeasureTheory Set ScarceTesting.PerfectTest

lemma key6 (a b : ℝ) (h : ¬ (a < 0 ∧ 0 < b)) :
    0 < max 0 a + max 0 b - max 0 (a + b) ↔ 0 < a ∧ b < 0 := by
  simp only [max_def]
  split_ifs <;> constructor <;> intro h' <;>
    first
    | (exfalso; linarith)
    | exact ⟨by linarith, by linarith⟩
    | (exfalso; apply h; exact ⟨by linarith, by linarith⟩)
    | linarith

theorem solution (f : ℝ → ℝ) (c κ φ σ : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (hφ0 : 0 ≤ φ) (hφσ : φ ≤ σ) (hσ1 : σ ≤ 1)
    (hσ0 : 0 < σ) (hφ1 : φ < 1)
    (hκ0 : 0 < κ) (hκ1 : κ < 1) (hf : IsPriorDensity f) :
    demand f c φ σ = cdf f (tH c φ σ) - cdf f (tL c φ σ) ∧
    availability κ (demand f c φ σ) = availThr f κ (tL c φ σ) (tH c φ σ) := by
  have h1c : 0 < 1 - c := by linarith
  have h1φ : 0 < 1 - φ := by linarith
  have hDL : 0 < c * φ + (1 - c) * σ := by positivity
  have hDH : 0 < c * (1 - φ) + (1 - c) * (1 - σ) := by
    have : 0 ≤ (1 - c) * (1 - σ) := mul_nonneg h1c.le (by linarith)
    have : 0 < c * (1 - φ) := by positivity
    linarith
  have hLc : c * φ ≤ c * (c * φ + (1 - c) * σ) := by
    nlinarith [mul_nonneg (mul_nonneg hc0.le h1c.le) (sub_nonneg.2 hφσ)]
  have hcH : c * (c * (1 - φ) + (1 - c) * (1 - σ)) ≤ c * (1 - φ) := by
    nlinarith [mul_nonneg (mul_nonneg hc0.le h1c.le) (sub_nonneg.2 hφσ)]
  have hL0 : 0 ≤ tL c φ σ := by unfold tL; positivity
  have hH1 : tH c φ σ ≤ 1 := by
    unfold tH
    rw [div_le_one hDH]
    nlinarith [mul_nonneg h1c.le (sub_nonneg.2 hσ1)]
  have hLc' : tL c φ σ ≤ c := by
    unfold tL; rw [div_le_iff₀ hDL]; nlinarith
  have hcH' : c ≤ tH c φ σ := by
    unfold tH; rw [le_div_iff₀ hDH]; nlinarith
  have hLH : tL c φ σ ≤ tH c φ σ := hLc'.trans hcH'
  -- characterisation of the request set
  have hreq : requestSet c φ σ = Ioo (tL c φ σ) (tH c φ σ) := by
    ext μ
    simp only [requestSet, mem_setOf_eq, mem_Ioo, mem_Icc]
    have hLiff : tL c φ σ < μ ↔ 0 < μ * σ - c * (μ * σ + (1 - μ) * φ) := by
      unfold tL
      rw [div_lt_iff₀ hDL]
      constructor <;> intro h <;> nlinarith
    have hHiff : μ < tH c φ σ ↔ μ * (1 - σ) - c * (μ * (1 - σ) + (1 - μ) * (1 - φ)) < 0 := by
      unfold tH
      rw [lt_div_iff₀ hDH]
      constructor <;> intro h <;> nlinarith
    have hV : 0 < Vtest c φ σ μ ↔ tL c φ σ < μ ∧ μ < tH c φ σ := by
      rw [hLiff, hHiff]
      unfold Vtest Utest UnoTest
      have hs : μ - c = (μ * σ - c * (μ * σ + (1 - μ) * φ)) +
          (μ * (1 - σ) - c * (μ * (1 - σ) + (1 - μ) * (1 - φ))) := by ring
      rw [hs]
      rw [← key6]
      · rintro ⟨ha, hb⟩
        have h1 : μ < tL c φ σ := by
          unfold tL; rw [lt_div_iff₀ hDL]; nlinarith
        have h2 : tH c φ σ < μ := by
          unfold tH; rw [div_lt_iff₀ hDH]; nlinarith
        linarith
    constructor
    · rintro ⟨_, h⟩; exact hV.1 h
    · intro h
      exact ⟨⟨hL0.trans h.1.le, h.2.le.trans hH1⟩, hV.2 h⟩
  have hdem : demand f c φ σ = cdf f (tH c φ σ) - cdf f (tL c φ σ) := by
    unfold demand
    rw [hreq, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hLH]
    unfold cdf
    have hi := hf.integrable
    have hsub : ∀ x ∈ Icc (0:ℝ) 1, IntervalIntegrable f volume 0 x := by
      intro x hx
      refine hi.mono_set ?_
      rw [uIcc_of_le zero_le_one, uIcc_of_le hx.1]
      exact Icc_subset_Icc le_rfl hx.2
    rw [intervalIntegral.integral_interval_sub_left
      (hsub _ ⟨hL0.trans hLH, hH1⟩) (hsub _ ⟨hL0, hLH.trans hH1⟩)]
  refine ⟨hdem, ?_⟩
  unfold availThr
  rw [hdem]
