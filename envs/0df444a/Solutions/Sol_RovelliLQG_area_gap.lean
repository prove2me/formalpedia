-- Prove2me | solution 1 for RovelliLQG.area_gap
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:23:38.793621+00:00
-- url     : https://prove2.me/submissions/fc68aa29-74da-451d-b161-9b04d7d14029

import Mathlib
import Definitions.Def_RovelliLQG_Defs

set_option autoImplicit false

open scoped InnerProductSpace

open RovelliLQG in
theorem solution :
    IsLeast {a : ℝ | ∃ k : ℕ, k ≠ 0 ∧ a = casimirRoot ((k : ℝ) / 2)} (Real.sqrt 3 / 2) := by
  have key : Real.sqrt 3 / 2 = Real.sqrt (3 / 4) := by
    rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4)]
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨⟨1, one_ne_zero, ?_⟩, ?_⟩
  · unfold casimirRoot
    rw [key]
    norm_num
  · rintro a ⟨k, hk, rfl⟩
    unfold casimirRoot
    rw [key]
    apply Real.sqrt_le_sqrt
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    nlinarith
