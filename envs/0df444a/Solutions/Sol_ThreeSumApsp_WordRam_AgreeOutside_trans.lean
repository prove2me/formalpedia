-- Prove2me | solution 1 for ThreeSumApsp.WordRam.AgreeOutside.trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:00.376183+00:00
-- url     : https://prove2.me/submissions/76307e13-83f4-4c08-ac26-c3acf208deca

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}
namespace ThreeSumApsp.WordRam
namespace AgreeOutside
theorem _root_.solution (h₁ : AgreeOutside s m₁ m₂) (h₂ : AgreeOutside s m₂ m₃) :
    AgreeOutside s m₁ m₃ :=
  Set.EqOn.trans h₂ h₁
end AgreeOutside
end ThreeSumApsp.WordRam
