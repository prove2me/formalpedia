-- Prove2me | solution 1 for ThreeSumApsp.WordRam.codeAt_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:42.429072+00:00
-- url     : https://prove2.me/submissions/5e3c9d9d-0cb6-4e78-acb2-3fbd58f2f183

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
namespace ThreeSumApsp.WordRam
theorem _root_.solution (l : List Instr) : CodeAt l 0 l := List.prefix_refl l
end ThreeSumApsp.WordRam
