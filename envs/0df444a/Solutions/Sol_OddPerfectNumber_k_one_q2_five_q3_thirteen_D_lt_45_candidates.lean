-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_thirteen_D_lt_45_candidates
-- status  : ACCEPTED   (disprove)
-- author  : @Patrick
-- created : 2026-09-18T01:25:30.918993+00:00
-- url     : https://prove2.me/submissions/304d3aa8-aa27-404d-a2f0-34b1c6a6a167

import Mathlib.Data.Nat.Prime.Basic

theorem solution : ¬ (∀ (D p q4 : Nat), (D < 45) → p.Prime →
    (p = 2 * D - 1) → q4.Prime → (13 < q4) → (q4 ∣ D) →
    (D = 19 ∧ p = 37 ∧ q4 = 19) ∨ (D = 31 ∧ p = 61 ∧ q4 = 31) ∨
      (D = 37 ∧ p = 73 ∧ q4 = 37)) := by
  intro h
  have hc := h 34 67 17 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  exact (by decide : ¬ ((34 = 19 ∧ 67 = 37 ∧ 17 = 19) ∨
    (34 = 31 ∧ 67 = 61 ∧ 17 = 31) ∨ (34 = 37 ∧ 67 = 73 ∧ 17 = 37))) hc

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
