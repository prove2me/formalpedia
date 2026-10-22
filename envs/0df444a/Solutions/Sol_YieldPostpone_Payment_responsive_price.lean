-- Prove2me | solution 1 for YieldPostpone.Payment.responsive_price
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:05:07.928455+00:00
-- url     : https://prove2.me/submissions/6d6d37c5-f49f-4793-981f-3e4f689cf63f

import Mathlib
import Definitions.Def_YieldPostpone_Payment_Setting
set_option autoImplicit false
open YieldPostpone.Payment

theorem solution (P : Params) (x : ℝ) (hP : P.Valid) (hx : 0 < x) :
    let p := if x < P.a / 2 then (P.a - x) / P.b else P.a / (2 * P.b)
    pAdm P p ∧ ∀ p', pAdm P p' → salesRev P p' x ≤ salesRev P p x := by
  obtain ⟨ha, hb, -, -, -, -⟩ := hP
  intro p
  by_cases hxa : x < P.a / 2
  · have hp : p = (P.a - x) / P.b := by simp only [p, if_pos hxa]
    rw [hp]
    set p0 := (P.a - x) / P.b with hp0
    have hbp : P.b * p0 = P.a - x := by rw [hp0]; field_simp
    have hpos : 0 < p0 := div_pos (by linarith) hb
    have hlt : p0 < P.a / P.b := by
      rw [hp0, div_lt_div_iff_of_pos_right hb]; linarith
    refine ⟨⟨hpos, hlt⟩, ?_⟩
    rintro p' ⟨hp'0, hp'1⟩
    unfold salesRev demand
    have h1 : P.a - P.b * p0 = x := by linarith
    rw [h1, min_self]
    rcases le_total p' p0 with h | h
    · have := min_le_right (P.a - P.b * p') x
      nlinarith
    · have hbp' : P.b * p0 ≤ P.b * p' := mul_le_mul_of_nonneg_left h hb.le
      have hxl : P.a - P.b * p' ≤ x := by linarith
      rw [min_eq_left hxl]
      have := mul_nonneg (sub_nonneg.2 h) (show 0 ≤ P.b * p' - x by linarith)
      have ha' : P.a = P.b * p0 + x := by linarith
      rw [ha']
      nlinarith
  · have hp : p = P.a / (2 * P.b) := by simp only [p, if_neg hxa]
    rw [hp]
    have hbp : P.b * (P.a / (2 * P.b)) = P.a / 2 := by field_simp
    have hpos : 0 < P.a / (2 * P.b) := by positivity
    have hlt : P.a / (2 * P.b) < P.a / P.b := by
      apply div_lt_div_of_pos_left ha hb; linarith
    refine ⟨⟨hpos, hlt⟩, ?_⟩
    rintro p' ⟨hp'0, hp'1⟩
    unfold salesRev demand
    set p0 := P.a / (2 * P.b)
    have h1 : P.a - P.b * p0 = P.a / 2 := by linarith
    have hx' : P.a / 2 ≤ x := not_lt.1 hxa
    rw [h1, min_eq_left hx']
    have := min_le_left (P.a - P.b * p') x
    have hq : p' * min (P.a - P.b * p') x ≤ p' * (P.a - P.b * p') :=
      mul_le_mul_of_nonneg_left this hp'0.le
    have hp0eq : P.b * p0 = P.a / 2 := hbp
    have hfin : p' * (P.a - P.b * p') ≤ p0 * (P.a / 2) := by
      have e : P.b * (p0 * (P.a / 2) - p' * (P.a - P.b * p')) = (P.b * p' - P.a / 2) ^ 2 := by
        have : P.b * (p0 * (P.a / 2)) = (P.b * p0) * (P.a / 2) := by ring
        nlinarith [hp0eq]
      have : 0 ≤ P.b * (p0 * (P.a / 2) - p' * (P.a - P.b * p')) := by rw [e]; positivity
      have := nonneg_of_mul_nonneg_right this hb
      linarith
    linarith
