-- Prove2me | solution 1 for ThreeSumApsp.WordRam.AgreeOutside.cell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:44.617563+00:00
-- url     : https://prove2.me/submissions/a0c613a6-6633-425d-9994-d52accc03c47

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
namespace AgreeOutside
theorem _root_.solution (h : AgreeOutside s m m') (ha : a ∉ s) : m' a = m a := h ha
end AgreeOutside
end ThreeSumApsp.WordRam
