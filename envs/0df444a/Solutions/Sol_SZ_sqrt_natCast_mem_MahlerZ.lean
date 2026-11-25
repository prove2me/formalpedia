-- Prove2me | solution 1 for SZ.sqrt_natCast_mem_MahlerZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:17:08.920482+00:00
-- url     : https://prove2.me/submissions/a2ade8b6-da31-4fce-8af3-99a20f98087a

import Definitions.Def_SZ_SliceHygiene
import Definitions.Def_SZ_SqrtTwo
import Definitions.Def_SZ_SqrtThree
import Definitions.Def_SZ_Tijdeman
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_Cells
import Theorems.Thm_SZ_sqrtFive_mem_MahlerZ
import Theorems.Thm_SZ_sqrtSix_mem_MahlerZ
import Theorems.Thm_SZ_sqrtSeven_mem_MahlerZ
import Theorems.Thm_SZ_sqrtEight_mem_MahlerZ
import Theorems.Thm_SZ_greedy_zero
import Theorems.Thm_SZ_mem_MahlerZ_of_three_le
import Theorems.Thm_SZ_natCast_mem_MahlerZ
import Theorems.Thm_SZ_sqrtThree_mem_MahlerZ
attribute [local simp] SZ.greedy_zero



set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution {m : ℕ} (hm : 2 ≤ m) (hne : m ≠ 2) :
    Real.sqrt m ∈ MahlerZ := by
  rcases le_or_gt 9 m with h9 | h9
  · refine mem_MahlerZ_of_three_le ?_
    have h : Real.sqrt 9 ≤ Real.sqrt m := Real.sqrt_le_sqrt (by exact_mod_cast h9)
    rwa [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)] at h
  · interval_cases m
    · exact absurd rfl hne
    · simpa using sqrtThree_mem_MahlerZ
    · have h4 : Real.sqrt ((4 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) := by
        rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
        norm_num
      rw [h4]
      exact natCast_mem_MahlerZ (le_refl 2)
    · simpa using sqrtFive_mem_MahlerZ
    · simpa using sqrtSix_mem_MahlerZ
    · simpa using sqrtSeven_mem_MahlerZ
    · simpa using sqrtEight_mem_MahlerZ
end SZ
