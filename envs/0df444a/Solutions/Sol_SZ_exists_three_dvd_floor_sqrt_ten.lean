-- Prove2me | solution 1 for SZ.exists_three_dvd_floor_sqrt_ten
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:40.523045+00:00
-- url     : https://prove2.me/submissions/b0503b60-2c73-4fca-b7b9-1ab7f78aadb9

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
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → (3 : ℤ) ∣ ⌊ξ * Real.sqrt 10 ^ n⌋ := by
  have h := exists_dvd_floor_sqrt 3 10 (by norm_num) (by norm_num)
    (not_isSquare_of_bounded (by norm_num) (by decide))
    (Or.inl ⟨by norm_num, by norm_num⟩)
  norm_num at h
  exact h
end SZ
