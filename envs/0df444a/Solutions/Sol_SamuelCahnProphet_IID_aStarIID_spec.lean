-- Prove2me | solution 1 for SamuelCahnProphet.IID.aStarIID_spec
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T21:44:35.451801+00:00
-- url     : https://prove2.me/submissions/7f2e1b0f-f68d-43b6-bccc-640c7aee65dc

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology


namespace SamuelCahnProphet.IID

theorem aStar_core (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (1 - Real.exp (-b - c)) * (b + aStarIID b c * c) / (b + c) = 1 - Real.exp (-b) ∧
      0 < aStarIID b c ∧ aStarIID b c < 1 := by
  have hx : Real.exp (-b) < 1 := by have := Real.exp_lt_exp.2 (show -b < 0 by linarith); simpa using this
  have hy : Real.exp (-c) < 1 := by have := Real.exp_lt_exp.2 (show -c < 0 by linarith); simpa using this
  have hxpos : 0 < Real.exp (-b) := Real.exp_pos _
  have hypos : 0 < Real.exp (-c) := Real.exp_pos _
  have hxy : Real.exp (-b - c) = Real.exp (-b) * Real.exp (-c) := by
    rw [sub_eq_add_neg, Real.exp_add]
  have hxy1 : Real.exp (-b) * Real.exp (-c) < 1 := by nlinarith
  have hD : 0 < c * (1 - Real.exp (-b - c)) := by rw [hxy]; apply mul_pos hc; linarith
  have hbc : 0 < b + c := by linarith
  -- key inequalities
  have h1 : b * Real.exp (-b) < 1 - Real.exp (-b) := by
    have := Real.add_one_lt_exp (x := b) hb.ne'
    have h2 : Real.exp b * Real.exp (-b) = 1 := by rw [← Real.exp_add]; simp
    nlinarith
  have h2 : 1 - Real.exp (-c) < c := by
    have := Real.add_one_lt_exp (x := -c) (by linarith)
    linarith
  unfold aStarIID
  refine ⟨?_, ?_, ?_⟩
  · have hne : 1 - Real.exp (-b - c) ≠ 0 := by rw [hxy]; linarith
    have hne2 : b + c ≠ 0 := hbc.ne'
    rw [hxy] at hne ⊢
    field_simp
    ring
  · apply div_pos _ hD
    have : b * Real.exp (-b) * (1 - Real.exp (-c)) < c * (1 - Real.exp (-b)) := by
      have h3 : 0 < 1 - Real.exp (-c) := by linarith
      calc b * Real.exp (-b) * (1 - Real.exp (-c)) < (1 - Real.exp (-b)) * (1 - Real.exp (-c)) := by
            exact mul_lt_mul_of_pos_right h1 h3
        _ < (1 - Real.exp (-b)) * c := mul_lt_mul_of_pos_left h2 (by linarith)
        _ = _ := by ring
    linarith
  · rw [div_lt_one hD]
    rw [hxy]
    have h3 : 0 < 1 - Real.exp (-c) := by linarith
    nlinarith [mul_pos hxpos h3, mul_pos hb (mul_pos hxpos h3), mul_pos hc (mul_pos hxpos h3)]

end SamuelCahnProphet.IID

open SamuelCahnProphet.IID


theorem solution (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (1 - Real.exp (-b - c)) * (b + aStarIID b c * c) / (b + c) = 1 - Real.exp (-b) ∧
      0 < aStarIID b c ∧ aStarIID b c < 1 := by
  exact aStar_core b c hb hc
