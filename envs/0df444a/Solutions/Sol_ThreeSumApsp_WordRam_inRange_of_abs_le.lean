-- Prove2me | solution 1 for ThreeSumApsp.WordRam.inRange_of_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:09:44.835347+00:00
-- url     : https://prove2.me/submissions/1b618b95-b6e8-46cc-bceb-eea50b18c3a3

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
theorem _root_.solution {v B : ℤ} (hB : 2 * B < (2 : ℤ) ^ W) (h : |v| ≤ B) : InRange W v := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  constructor <;> linarith
end ThreeSumApsp.WordRam
