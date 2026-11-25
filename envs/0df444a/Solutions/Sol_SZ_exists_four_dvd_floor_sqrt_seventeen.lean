-- Prove2me | solution 1 for SZ.exists_four_dvd_floor_sqrt_seventeen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:58.680886+00:00
-- url     : https://prove2.me/submissions/e094de5f-c775-4aeb-b8b1-5f57afbc39d6

import Definitions.Def_SZ_SliceHygiene
import Mathlib.Tactic.Push
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_ThmC
import Theorems.Thm_SZ_exists_dvd_floor_sqrt
import Theorems.Thm_SZ_not_isSquare_of_bounded


set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → (4 : ℤ) ∣ ⌊ξ * Real.sqrt 17 ^ n⌋ := by
  have h := exists_dvd_floor_sqrt 4 17 (by norm_num) (by norm_num)
    (not_isSquare_of_bounded (by norm_num) (by decide))
    (Or.inl ⟨by norm_num, by norm_num⟩)
  norm_num at h
  exact h
end SZ
