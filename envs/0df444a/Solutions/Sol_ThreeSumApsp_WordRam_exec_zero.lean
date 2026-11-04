-- Prove2me | solution 1 for ThreeSumApsp.WordRam.exec_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:09:48.442835+00:00
-- url     : https://prove2.me/submissions/659d6779-611d-4d24-922f-322ef44b59ec

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
theorem _root_.solution (c : Cfg W) : exec P 0 c.pc c.mem = none := by rw [exec]
end ThreeSumApsp.WordRam
