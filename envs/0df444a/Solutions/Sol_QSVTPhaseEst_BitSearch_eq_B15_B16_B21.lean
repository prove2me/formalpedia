-- Prove2me | solution 1 for QSVTPhaseEst.BitSearch.eq_B15_B16_B21
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T14:52:47.047223+00:00
-- url     : https://prove2.me/submissions/8836268f-bc14-415c-87c9-07742a5150c7

import Mathlib
import Definitions.Def_QSVTPhaseEst_BitSearch_Procedure

open QSVTPhaseEst.BitSearch in
theorem solution (Δ : ℝ) (hΔ0 : 0 ≤ Δ) :
    (1 / 4 - Real.arccos (1 / Real.sqrt 2 + Δ / 2) / Real.pi < 1 / 16 ↔
        Δ < 2 * (Real.cos (3 * Real.pi / 16) - 1 / Real.sqrt 2)) ∧
      (Δ < 2 * (Real.cos (3 * Real.pi / 16) - 1 / Real.sqrt 2) →
        |Real.arccos (1 / Real.sqrt 2 + Δ / 2) / Real.pi - 1 / 4| < 1 / 16 ∧
        |Real.arccos (1 / Real.sqrt 2 - Δ / 2) / Real.pi - 1 / 4| < 1 / 16) := by
  have hπ := Real.pi_pos
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hinv : 1 / Real.sqrt 2 = Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four, div_eq_div_iff hs2.ne' two_ne_zero]
    linarith
  have hinvpos : 0 < 1 / Real.sqrt 2 := by positivity
  have hinvlt : 1 / Real.sqrt 2 < 1 := by
    rw [div_lt_one hs2]
    nlinarith [Real.sqrt_nonneg 2]
  have hc3 : Real.arccos (Real.cos (3 * Real.pi / 16)) = 3 * Real.pi / 16 :=
    Real.arccos_cos (by positivity) (by linarith)
  have hc5 : Real.arccos (Real.cos (5 * Real.pi / 16)) = 5 * Real.pi / 16 :=
    Real.arccos_cos (by positivity) (by linarith)
  have hc4 : Real.arccos (1 / Real.sqrt 2) = Real.pi / 4 := by
    rw [hinv]; exact Real.arccos_cos (by positivity) (by linarith)
  have hcos3le : Real.cos (3 * Real.pi / 16) ≤ 1 := Real.cos_le_one _
  have hcos5pos : 0 < Real.cos (5 * Real.pi / 16) := by
    apply Real.cos_pos_of_mem_Ioo; constructor <;> linarith
  -- key bound cos(3π/16) + cos(5π/16) ≤ √2
  have hsum : Real.cos (3 * Real.pi / 16) + Real.cos (5 * Real.pi / 16) ≤ Real.sqrt 2 := by
    rw [Real.cos_add_cos]
    have e1 : (3 * Real.pi / 16 + 5 * Real.pi / 16) / 2 = Real.pi / 4 := by ring
    rw [e1, Real.cos_pi_div_four]
    have := Real.cos_le_one ((3 * Real.pi / 16 - 5 * Real.pi / 16) / 2)
    nlinarith
  set a := 1 / Real.sqrt 2 + Δ / 2 with ha
  have hapos : 0 < a := by positivity
  have hiff : 1 / 4 - Real.arccos a / Real.pi < 1 / 16 ↔ a < Real.cos (3 * Real.pi / 16) := by
    constructor
    · intro h
      by_contra hge
      push_neg at hge
      have h1 : Real.arccos a ≤ 3 * Real.pi / 16 := by
        rw [← hc3]; exact Real.arccos_le_arccos hge
      have h2 : Real.arccos a / Real.pi ≤ 3 / 16 := by
        rw [div_le_iff₀ hπ]; linarith
      linarith
    · intro h
      have h1 : 3 * Real.pi / 16 < Real.arccos a := by
        rw [← hc3]; exact Real.arccos_lt_arccos (by linarith) h hcos3le
      have h2 : 3 / 16 < Real.arccos a / Real.pi := by
        rw [lt_div_iff₀ hπ]; linarith
      linarith
  have hΔiff : a < Real.cos (3 * Real.pi / 16) ↔
      Δ < 2 * (Real.cos (3 * Real.pi / 16) - 1 / Real.sqrt 2) := by
    rw [ha]; constructor <;> intro h <;> linarith
  refine ⟨hiff.trans hΔiff, fun hΔ => ?_⟩
  have halt : a < Real.cos (3 * Real.pi / 16) := hΔiff.mpr hΔ
  constructor
  · have h1 : 3 * Real.pi / 16 < Real.arccos a := by
      rw [← hc3]; exact Real.arccos_lt_arccos (by linarith) halt hcos3le
    have h2 : Real.arccos a ≤ Real.pi / 4 := by
      rw [← hc4]; exact Real.arccos_le_arccos (by rw [ha]; linarith)
    have h3 : 3 / 16 < Real.arccos a / Real.pi := by rw [lt_div_iff₀ hπ]; linarith
    have h4 : Real.arccos a / Real.pi ≤ 1 / 4 := by rw [div_le_iff₀ hπ]; linarith
    rw [abs_lt]; constructor <;> linarith
  · set b := 1 / Real.sqrt 2 - Δ / 2 with hb
    have hb1 : b ≤ 1 / Real.sqrt 2 := by rw [hb]; linarith
    have hinv2 : 1 / Real.sqrt 2 + 1 / Real.sqrt 2 = Real.sqrt 2 := by
      field_simp
      linarith
    have hb5 : Real.cos (5 * Real.pi / 16) < b := by
      rw [hb]; linarith
    have h1 : Real.arccos b < 5 * Real.pi / 16 := by
      rw [← hc5]; exact Real.arccos_lt_arccos (by linarith) hb5 (by linarith)
    have h2 : Real.pi / 4 ≤ Real.arccos b := by
      rw [← hc4]; exact Real.arccos_le_arccos hb1
    have h3 : Real.arccos b / Real.pi < 5 / 16 := by rw [div_lt_iff₀ hπ]; linarith
    have h4 : 1 / 4 ≤ Real.arccos b / Real.pi := by rw [le_div_iff₀ hπ]; linarith
    rw [abs_lt]; constructor <;> linarith
