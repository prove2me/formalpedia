-- Prove2me | solution 1 for SZ.sqrtFive_mem_MahlerZ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:02:08.711495+00:00
-- url     : https://prove2.me/submissions/1dc299b5-df13-4281-a336-bc0cd1dbda01

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
theorem _root_.solution : Real.sqrt 5 ∈ MahlerZ := by
  have hM : slice5.M = 1 := by norm_num [Slice.M, slice5]
  have hsq : slice5.sq = Real.sqrt 5 := by norm_num [Slice.sq, slice5]
  have hp : (slice5.p : ℝ) = 2 := by norm_num [slice5]
  have hU : slice5.U = 1 + Real.sqrt 5 := rfl
  have hσ : slice5.sigma 2 1 = 3 * Real.sqrt 5 - 4 := by
    rw [Slice.sigma, hM, hsq, hp]; push_cast; ring
  have h := Slice.mem_MahlerZ_of_uniform slice5 rfl (by norm_num [slice5])
    (by rw [hsq, hp]; have := s5_lb; linarith)
    (j := 2) (k₀ := 1) (by norm_num) (by norm_num)
    (by rw [hσ]; have := s5_lb; linarith)
    (by rw [hσ, hU]; have := s5_ub; linarith)
  norm_num [slice5] at h
  exact h
end SZ
