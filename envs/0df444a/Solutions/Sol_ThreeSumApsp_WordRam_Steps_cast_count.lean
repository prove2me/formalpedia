-- Prove2me | solution 1 for ThreeSumApsp.WordRam.Steps.cast_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:13:16.398384+00:00
-- url     : https://prove2.me/submissions/110f0ade-15c4-4076-8bc3-e8f8f6413c68

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
namespace Steps
theorem _root_.solution {n n' : ℕ} {c c' : Cfg W} (h : Steps P n c c') (hn : n = n') :
    Steps P n' c c' := hn ▸ h
end Steps
end ThreeSumApsp.WordRam
