-- Prove2me | solution 1 for ThreeSumApsp.WordRam.effect_store
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:09:06.999344+00:00
-- url     : https://prove2.me/submissions/a25d27ab-db53-4c9e-be75-33bf79ee58ca

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
theorem _root_.solution (j : ℤ) (hi : m i = wd W a) (ha : InRange W a) :
    effect (.store i j) m = Function.update m a (m j) := by
  rw [effect, hi, toInt_wd ha]
end ThreeSumApsp.WordRam
