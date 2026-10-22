-- Prove2me | solution 1 for PostTruth.Regimes.threshold_gap
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:04:25.948049+00:00
-- url     : https://prove2.me/submissions/5c85df81-9b81-4b13-8e12-29422dc63781

import Mathlib
import Definitions.Def_PostTruth_Regimes_Model
set_option autoImplicit false
open PostTruth.Regimes

theorem solution (p q : ℝ) (hpq : Standing p q) :
    gap p q - rTilde p q = (2 * p * (1 - q) - 1) / (2 * q) ∧
    (gap p q - rTilde p q = 0 ↔ q = qStar p) ∧
    (gap p q - rTilde p q < 0 ↔ qStar p < q) ∧
    StrictAntiOn (fun t : ℝ => (2 * p * (1 - t) - 1) / (2 * t))
      (Set.Ioi 0) := by
  obtain ⟨hp1, hp2, hq0, hq1⟩ := hpq
  have hp0 : 0 < p := by linarith
  have hmain : gap p q - rTilde p q = (2 * p * (1 - q) - 1) / (2 * q) := by
    unfold gap rTilde
    field_simp
    ring
  refine ⟨hmain, ?_, ?_, ?_⟩
  · rw [hmain, div_eq_zero_iff]
    unfold qStar
    constructor
    · rintro (h | h)
      · rw [eq_div_iff (by positivity)]; linarith
      · linarith
    · intro h
      left
      rw [eq_div_iff (by positivity)] at h; linarith
  · rw [hmain, div_lt_iff₀ (by positivity)]
    unfold qStar
    rw [div_lt_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  · intro s hs t ht hst
    simp only [Set.mem_Ioi] at hs ht
    show (2 * p * (1 - t) - 1) / (2 * t) < (2 * p * (1 - s) - 1) / (2 * s)
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hs ht, sub_pos.2 hst]
