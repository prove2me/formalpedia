-- Prove2me | solution 1 for SZ.exists_five_dvd_floor_sqrt_twentySix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:05:02.033738+00:00
-- url     : https://prove2.me/submissions/dbd4b175-c2a7-4a1f-ac7e-ef4d83de26a7

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
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → (5 : ℤ) ∣ ⌊ξ * Real.sqrt 26 ^ n⌋ := by
  have h := exists_dvd_floor_sqrt 5 26 (by norm_num) (by norm_num)
    (not_isSquare_of_bounded (by norm_num) (by decide))
    (Or.inl ⟨by norm_num, by norm_num⟩)
  norm_num at h
  exact h
end SZ
