-- Prove2me | solution 1 for SZ.sqrtSeven_mem_MahlerZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:09.891424+00:00
-- url     : https://prove2.me/submissions/7fb0df36-6b7d-4115-ae57-df7079169437

import Definitions.Def_SZ_SliceHygiene
import Definitions.Def_SZ_SqrtTwo
import Definitions.Def_SZ_SqrtThree
import Definitions.Def_SZ_Tijdeman
import Mathlib.Tactic.IntervalCases
import Definitions.Def_SZ_Cells
import Theorems.Thm_SZ_Slice_mem_MahlerZ_of_uniform


set_option autoImplicit false
open SZ
namespace SZ
theorem _root_.solution : Real.sqrt 7 ∈ MahlerZ := by
  have hM : slice7.M = 1 := by norm_num [Slice.M, slice7]
  have hsq : slice7.sq = Real.sqrt 7 := by norm_num [Slice.sq, slice7]
  have hp : (slice7.p : ℝ) = 2 := by norm_num [slice7]
  have hU : slice7.U = 1 + Real.sqrt 7 := rfl
  have hσ : slice7.sigma 3 1 = 3 * Real.sqrt 7 - 6 := by
    rw [Slice.sigma, hM, hsq, hp]; push_cast; ring
  have h := Slice.mem_MahlerZ_of_uniform slice7 rfl (by norm_num [slice7])
    (by rw [hsq, hp]; have := s7_lb; linarith)
    (j := 3) (k₀ := 1) (by norm_num) (by norm_num)
    (by rw [hσ]; have := s7_lb; linarith)
    (by rw [hσ, hU]; have := s7_ub; linarith)
  norm_num [slice7] at h
  exact h
end SZ
