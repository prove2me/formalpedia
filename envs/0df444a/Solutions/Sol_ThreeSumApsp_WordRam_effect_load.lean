-- Prove2me | solution 1 for ThreeSumApsp.WordRam.effect_load
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:09:05.858652+00:00
-- url     : https://prove2.me/submissions/eacfff18-f41b-49cd-84ca-de5409a52e24

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Theorems.Thm_ThreeSumApsp_WordRam_toInt_wd

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
variable {m : ℤ → BitVec W} {i j k a b : ℤ}
namespace ThreeSumApsp.WordRam
theorem _root_.solution (i : ℤ) (hj : m j = wd W a) (ha : InRange W a) :
    effect (.load i j) m = Function.update m i (m a) := by
  rw [effect, hj, toInt_wd ha]
end ThreeSumApsp.WordRam
