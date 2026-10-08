-- Prove2me | solution 1 for WeightedRootIntegralIdentity.missionDataConsequences
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T10:47:39.389447+00:00
-- url     : https://prove2.me/submissions/e34600a7-6460-4dad-b549-f4bbd3e0f0e9

import Mathlib
open scoped Interval

theorem solution
    (n : ℕ) (hn : 2 ≤ n) (a : ℕ → ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1)) :
    (∀ k < n - 1, a k ≤ a (k + 1)) ∧
    (∀ k < n - 1, ∀ x ∈ Set.Ioo (a k) (a (k + 1)), 0 < x ∧ x ≠ 0) := by
  constructor
  · intro k hk
    exact hmono k hk
  · intro k hk x hx
    have hklt : k < n := by omega
    have hpk : 0 < a k := hpos k hklt
    have hxpos : 0 < x := lt_trans hpk hx.1
    exact ⟨hxpos, ne_of_gt hxpos⟩
