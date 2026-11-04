-- Prove2me | solution 1 for ThreeSumApsp.WordRam.effects_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:57.451425+00:00
-- url     : https://prove2.me/submissions/4f7384de-3494-4a1a-ab5d-6d36680e1dec

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
theorem _root_.solution (m : ℤ → BitVec W) : effects [] m = m := rfl
end ThreeSumApsp.WordRam
