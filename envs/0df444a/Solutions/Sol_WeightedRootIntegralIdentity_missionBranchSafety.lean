-- Prove2me | solution 1 for WeightedRootIntegralIdentity.missionBranchSafety
-- status  : ACCEPTED   (prove)
-- author  : @abcdefg
-- created : 2026-09-20T10:44:02.948067+00:00
-- url     : https://prove2.me/submissions/efed0cc6-f77b-40c9-98c0-87d358fb294d

import Mathlib
open scoped Interval

theorem solution
    (n : ℕ) (a : ℕ → ℝ) (k : ℕ) (x : ℝ)
    (hpos : ∀ i < n, 0 < a i)
    (hmono : ∀ i < n - 1, a i ≤ a (i + 1))
    (hk : k + 1 < n)
    (hx : x ∈ Set.Ioo (a k) (a (k + 1))) :
    x ≠ 0 ∧ a k ≤ a (k + 1) := by
  have hklt : k < n := by omega
  have hkpred : k < n - 1 := by omega
  have hpk : 0 < a k := hpos k hklt
  have hxpos : 0 < x := lt_of_lt_of_le hpk (le_of_lt hx.1)
  constructor
  · exact ne_of_gt hxpos
  · exact hmono k hkpred
