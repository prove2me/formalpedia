-- Prove2me | solution 1 for ThreeSumApsp.WordRam.loadWords_mem_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:09:46.07343+00:00
-- url     : https://prove2.me/submissions/fb48f255-243c-4502-818c-41cf2d741f43

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
theorem _root_.solution (W : ℕ) (ws : List ℤ) (a : ℕ) :
    loadWords W ws (a : ℤ) = wd W (ws.getD a 0) := by
  simp [loadWords, show ¬ ((a : ℤ) < 0) by omega]
end ThreeSumApsp.WordRam
