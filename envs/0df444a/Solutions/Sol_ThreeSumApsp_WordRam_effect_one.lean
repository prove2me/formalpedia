-- Prove2me | solution 1 for ThreeSumApsp.WordRam.effect_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:13:40.186508+00:00
-- url     : https://prove2.me/submissions/dd7cac1c-af5e-444c-86b1-482c00bf75f6

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
variable {m : ℤ → BitVec W} {i j k a b : ℤ}
namespace ThreeSumApsp.WordRam
theorem _root_.solution (i : ℤ) : effect (.one i) m = Function.update m i (wd W 1) := rfl
end ThreeSumApsp.WordRam
