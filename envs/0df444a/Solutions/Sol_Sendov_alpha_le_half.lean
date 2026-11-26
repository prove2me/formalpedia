-- Prove2me | solution 1 for Sendov.alpha_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:49:09.284581+00:00
-- url     : https://prove2.me/submissions/c5e02bd9-60b8-44d5-86c2-d6f2a99e4b3b

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_Reduction_Setup
import Theorems.Thm_Sendov_M_pos


set_option autoImplicit false
open Sendov
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) :
    α ≤ M n / 2 := by
  have hM : 0 < M n := M_pos hn
  rw [hα]
  nlinarith [sq_nonneg a]
end Sendov
