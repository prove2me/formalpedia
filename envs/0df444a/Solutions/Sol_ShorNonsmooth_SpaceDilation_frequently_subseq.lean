-- Prove2me | solution 1 for ShorNonsmooth.SpaceDilation.frequently_subseq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:26:15.634471+00:00
-- url     : https://prove2.me/submissions/9b49072d-ac1e-46e2-bec8-3917ec4c6038

import Mathlib


theorem solution (Q : ℕ → Prop)
    (h : ∀ J : ℕ, ∃ j : ℕ, J ≤ j ∧ Q j) :
    ∃ kp : ℕ → ℕ, StrictMono kp ∧ ∀ p : ℕ, Q (kp p) := by
  have hf : ∃ᶠ n in Filter.atTop, Q n := Filter.frequently_atTop.mpr h
  exact Filter.extraction_of_frequently_atTop hf
