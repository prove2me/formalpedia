-- Prove2me | solution 1 for RhinViola.lemma3BaseCaseClassification
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:16:01.536063+00:00
-- url     : https://prove2.me/submissions/6e0042a4-ef92-44d1-8e6a-280596d829ac

import Mathlib
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.all false

theorem solution
    (k l nu r : ℕ) (hbal : nu + r = k + l)
    (hzero : k = 0 ∨ l = 0 ∨ nu = 0 ∨ r = 0) :
    nu = 0 ∨
      (l = 0 ∧ nu ≤ k) ∨
      (k = 0 ∧ nu ≤ l) ∨
      (r = 0 ∧ 0 < k ∧ 0 < l ∧ nu = k + l ∧ k < nu ∧ l < nu) := by
  intros
  omega
