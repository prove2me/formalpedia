-- Prove2me | solution 1 for ThreeSumApsp.WordRam.CodeAt.tail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:39.138113+00:00
-- url     : https://prove2.me/submissions/776b0f59-12fe-4b27-9ef4-1a9a4f577672

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_right

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
namespace ThreeSumApsp.WordRam
namespace CodeAt
theorem _root_.solution {pos : ℕ} {i : Instr} {l : List Instr} (h : CodeAt P pos (i :: l)) :
    CodeAt P (pos + 1) l :=
  CodeAt.right (l₁ := [i]) h
end CodeAt
end ThreeSumApsp.WordRam
