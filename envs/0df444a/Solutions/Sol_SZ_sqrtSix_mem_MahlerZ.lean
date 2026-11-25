-- Prove2me | solution 1 for SZ.sqrtSix_mem_MahlerZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:30.287555+00:00
-- url     : https://prove2.me/submissions/6382d17a-c22d-45ab-af1c-bda00ce5dd2a

import Definitions.Def_SZ_SliceHygiene
import Definitions.Def_SZ_SqrtTwo
import Definitions.Def_SZ_SqrtThree
import Definitions.Def_SZ_Tijdeman
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_Cells
import Theorems.Thm_SZ_Slice_mem_MahlerZ_of_e_le


set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : Real.sqrt 6 ∈ MahlerZ := by
  have hM : slice6.M = 4 / 5 := by norm_num [Slice.M, slice6]
  have hsq : slice6.sq = Real.sqrt 6 := by norm_num [Slice.sq, slice6]
  have hp : (slice6.p : ℝ) = 2 := by norm_num [slice6]
  have hU : slice6.U = 4 * (1 + Real.sqrt 6) / 5 := rfl
  have hσ : slice6.sigma 3 1 = 14 / 5 * Real.sqrt 6 - 6 := by
    rw [Slice.sigma, hM, hsq, hp]; push_cast; ring
  have h := Slice.mem_MahlerZ_of_e_le slice6 rfl (by norm_num [slice6])
    (j := 3) (k₀ := 1) (by norm_num)
    (by rw [hσ]; have := s6_lb; linarith)
    (by rw [hσ, hU]; have := s6_ub; linarith)
  norm_num [slice6] at h
  exact h
end SZ
