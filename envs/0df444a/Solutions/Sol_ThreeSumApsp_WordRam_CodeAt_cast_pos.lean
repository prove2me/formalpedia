-- Prove2me | solution 1 for ThreeSumApsp.WordRam.CodeAt.cast_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:03:26.49518+00:00
-- url     : https://prove2.me/submissions/eef6a4d0-eacb-4007-bb03-9c8d8a5b30c3

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
namespace CodeAt
theorem _root_.solution {pos pos' : ℕ} {l : List Instr} (h : CodeAt P pos l) (hp : pos = pos') :
    CodeAt P pos' l := hp ▸ h
end CodeAt
end ThreeSumApsp.WordRam
