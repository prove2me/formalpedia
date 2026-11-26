-- Prove2me | solution 1 for Sendov.alpha_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:15:14.405372+00:00
-- url     : https://prove2.me/submissions/0a8496ce-f925-48e5-9187-45e4d6b604e5

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_Reduction_Setup
import Theorems.Thm_Sendov_M_pos


set_option autoImplicit false
open Sendov
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (ha1 : a < 1) (_ha0 : 0 ≤ a)
    (hα : α = M n * (1 - a ^ 2) / 2) : 0 < α := by
  have hM : 0 < M n := M_pos hn
  rw [hα]
  have : 0 < 1 - a ^ 2 := by nlinarith
  positivity
end Sendov
