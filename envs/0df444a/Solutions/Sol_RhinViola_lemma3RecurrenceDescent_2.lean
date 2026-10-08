-- Prove2me | solution 2 for RhinViola.lemma3RecurrenceDescent
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T16:52:29.982297+00:00
-- url     : https://prove2.me/submissions/a5f4757b-5f1e-4b72-a84a-7c28bdf67129

import Mathlib.Tactic

theorem solution
    (k l nu r : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hnu : 0 < nu) (hr : 0 < r)
    (hbal : nu + r = k + l) :
    (((nu - 1) + (r - 1) = (k - 1) + (l - 1)) ∧
      (k - 1) + (l - 1) + (nu - 1) + (r - 1) < k + l + nu + r) ∧
    ((nu + (r - 1) = k + (l - 1)) ∧
      k + (l - 1) + nu + (r - 1) < k + l + nu + r) ∧
    ((nu + (r - 1) = (k - 1) + l) ∧
      (k - 1) + l + nu + (r - 1) < k + l + nu + r) := by
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
