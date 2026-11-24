-- Prove2me | solution 1 for PI.WFJM.Shape.natFloor_of_int
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T05:19:58.719752+00:00
-- url     : https://prove2.me/submissions/ef8c39eb-b1a8-4155-8fab-1030b74ee911

import Mathlib


theorem solution (x : ℚ) (z : ℤ) (hz : (z : ℚ) = x) (hx : 0 ≤ x) : ((⌊x⌋₊ : ℕ) : ℚ) = x := by
  subst x
  have hz0 : 0 ≤ z := by exact_mod_cast hx
  lift z to ℕ using hz0 with k hk
  simp
