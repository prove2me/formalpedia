-- Prove2me | solution 1 for ThreeSumApsp.WordRam.CodeAt.left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:17.378763+00:00
-- url     : https://prove2.me/submissions/fc145232-3d16-48ad-acde-7f6ea9500985

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
namespace ThreeSumApsp.WordRam
namespace CodeAt
theorem _root_.solution {pos : ℕ} {l₁ l₂ : List Instr} (h : CodeAt P pos (l₁ ++ l₂)) :
    CodeAt P pos l₁ :=
  (List.prefix_append l₁ l₂).trans h
end CodeAt
end ThreeSumApsp.WordRam
