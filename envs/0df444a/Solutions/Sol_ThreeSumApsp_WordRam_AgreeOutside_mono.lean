-- Prove2me | solution 1 for ThreeSumApsp.WordRam.AgreeOutside.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:02:16.31054+00:00
-- url     : https://prove2.me/submissions/ac5fdd36-f983-4c88-9baa-f5429cd4373c

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
theorem _root_.solution (h : AgreeOutside s m m') (hst : s ⊆ t) : AgreeOutside t m m' :=
  Set.EqOn.mono (Set.compl_subset_compl.2 hst) h
end AgreeOutside
end ThreeSumApsp.WordRam
