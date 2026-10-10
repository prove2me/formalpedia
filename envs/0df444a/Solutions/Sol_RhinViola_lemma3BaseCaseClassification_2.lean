-- Prove2me | solution 2 for RhinViola.lemma3BaseCaseClassification
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-10T05:07:45.017701+00:00
-- url     : https://prove2.me/submissions/6a2696d6-9e49-4615-b9c6-3fc7e6c64d5c

import Mathlib.Tactic

theorem solution
    (k l nu r : ℕ) (hbal : nu + r = k + l)
    (hzero : k = 0 ∨ l = 0 ∨ nu = 0 ∨ r = 0) :
    nu = 0 ∨
      (l = 0 ∧ nu ≤ k) ∨
      (k = 0 ∧ nu ≤ l) ∨
      (r = 0 ∧ 0 < k ∧ 0 < l ∧ nu = k + l ∧ k < nu ∧ l < nu) := by
  rcases hzero with h | h | h | h <;> omega
