-- Prove2me | solution 1 for SystemicDiv.SellOff.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T01:54:07.021074+00:00
-- url     : https://prove2.me/submissions/8b184edf-a908-47bb-8204-fc56a3879934

import Mathlib
import Definitions.Def_SystemicDiv_SellOff_Model

open SystemicDiv.SellOff in
theorem solution (b : Bank) (hb : b.Standing) (R : ℝ) :
    (Liquidates b R ↔ R + b.ell < 0) ∧
      sold b R = b.levM * b.w * max (-(R + b.ell)) 0 := by
  obtain ⟨hw, hl, hlm, hM⟩ := hb
  have hMw : 0 < b.levM * b.w := mul_pos hM hw
  have key : (1 + b.levM) * b.d - b.levM * (b.w * (1 + R)) =
      b.levM * b.w * (-(R + b.ell)) := by
    unfold Bank.d Bank.ell
    have : (1 + b.lev) ≠ 0 := by positivity
    have : b.levM ≠ 0 := hM.ne'
    field_simp
    ring
  have hamt : amount b R = b.levM * b.w * (-(R + b.ell)) := by
    unfold amount; rw [← key]; ring
  have hliq : Liquidates b R ↔ R + b.ell < 0 := by
    unfold Liquidates
    constructor
    · intro h
      have h1 : 0 < b.levM * b.w * (-(R + b.ell)) := by linarith
      have h2 : 0 < -(R + b.ell) := pos_of_mul_pos_right h1 hMw.le
      linarith
    · intro h
      have : 0 < b.levM * b.w * (-(R + b.ell)) := mul_pos hMw (by linarith)
      linarith
  refine ⟨hliq, ?_⟩
  unfold sold
  by_cases h : Liquidates b R
  · rw [if_pos h, hamt, max_eq_left (by linarith [hliq.mp h])]
  · rw [if_neg h]
    have : 0 ≤ R + b.ell := by
      by_contra hc; push_neg at hc; exact h (hliq.mpr hc)
    rw [max_eq_right (by linarith)]
    ring
