-- Prove2me | solution 1 for ThreeSumApsp.WordRam.WritesIn.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:02:17.420199+00:00
-- url     : https://prove2.me/submissions/e0bc8b5f-09db-47da-9ca0-8a76cc626fc6

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
variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}
namespace ThreeSumApsp.WordRam
namespace WritesIn
theorem _root_.solution {i : Instr} (h : WritesIn s i) (hst : s ⊆ t) : WritesIn t i := by
  cases i <;> first | exact hst h | exact h
end WritesIn
end ThreeSumApsp.WordRam
