-- Prove2me | solution 1 for Sendov.c_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:51:14.545172+00:00
-- url     : https://prove2.me/submissions/0278f380-b310-4633-b735-17dc11c3e4d5

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_LargeDegree_Tail
import Theorems.Thm_Sendov_M_pos
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hα : 0 ≤ α) : c n α ≤ 1 := by
  have hM : 0 < M n := M_pos hn
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  simp only [c]
  have h1 : 0 ≤ α / M n := by positivity
  have h2 : 0 ≤ α / (2 * (3 + α)) := by positivity
  linarith
end Sendov
