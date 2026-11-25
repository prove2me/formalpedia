-- Prove2me | solution 1 for SZ.sqrtEight_mem_MahlerZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:36.483187+00:00
-- url     : https://prove2.me/submissions/3cbab5fd-dd63-4612-a3e6-d8123b6fd230

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
theorem _root_.solution : Real.sqrt 8 ∈ MahlerZ := by
  have hM : slice8.M = 6 / 7 := by norm_num [Slice.M, slice8]
  have hsq : slice8.sq = Real.sqrt 8 := by norm_num [Slice.sq, slice8]
  have hp : (slice8.p : ℝ) = 2 := by norm_num [slice8]
  have hU : slice8.U = 6 * (1 + Real.sqrt 8) / 7 := rfl
  have hσ : slice8.sigma 3 1 = 20 / 7 * Real.sqrt 8 - 6 := by
    rw [Slice.sigma, hM, hsq, hp]; push_cast; ring
  have h := Slice.mem_MahlerZ_of_e_le slice8 rfl (by norm_num [slice8])
    (j := 3) (k₀ := 1) (by norm_num)
    (by rw [hσ]; have := s8_lb; linarith)
    (by rw [hσ, hU]; have := s8_ub; linarith)
  norm_num [slice8] at h
  exact h
end SZ
