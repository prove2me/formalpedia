-- Prove2me | solution 1 for SZ.exists_three_dvd_floor_sqrt_twelve
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:42.037731+00:00
-- url     : https://prove2.me/submissions/4d106b79-388d-492b-aa18-1c8aaeeda2e6

import Definitions.Def_SZ_SliceHygiene
import Mathlib.Tactic.Push
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_ThmC
import Theorems.Thm_SZ_exists_dvd_floor_sqrt
import Theorems.Thm_SZ_not_isSquare_of_bounded

section
namespace SZ
private theorem s12_lb : (2.7 : ℝ) < Real.sqrt 12 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
end SZ
end

set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution :
    ∃ ξ : ℝ, 0 < ξ ∧ ∀ n : ℕ, 1 ≤ n → (3 : ℤ) ∣ ⌊ξ * Real.sqrt 12 ^ n⌋ := by
  have h := exists_dvd_floor_sqrt 3 12 (by norm_num) (by norm_num)
    (not_isSquare_of_bounded (by norm_num) (by decide))
    (Or.inr ⟨by norm_num, by have := s12_lb; norm_num; linarith⟩)
  norm_num at h
  exact h
end SZ
