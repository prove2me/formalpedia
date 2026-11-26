-- Prove2me | solution 1 for Sendov.A_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:44:52.19957+00:00
-- url     : https://prove2.me/submissions/ff5f1b17-dd08-4710-a395-c06ad9662749

import Definitions.Def_Sendov_Common_Chord
import Definitions.Def_Sendov_Reduction_Setup
import Theorems.Thm_Sendov_M_pos


set_option autoImplicit false
open Sendov
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hα : α = M n * (1 - a ^ 2) / 2) : A n α = a ^ 2 := by
  have hM : M n ≠ 0 := (M_pos hn).ne'
  simp only [A, hα]
  field_simp
  ring
end Sendov
