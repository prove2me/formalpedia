-- Prove2me | solution 1 for ThreeSumApsp.WordRam.effects_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:58.448442+00:00
-- url     : https://prove2.me/submissions/af419255-fba8-49b3-83e1-33f12de7b6b5

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
theorem _root_.solution (i : Instr) (l : List Instr) (m : ℤ → BitVec W) :
    effects (i :: l) m = effects l (effect i m) := rfl
end ThreeSumApsp.WordRam
