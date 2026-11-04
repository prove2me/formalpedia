-- Prove2me | solution 1 for ThreeSumApsp.WordRam.AgreeOutside.refl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:03:27.643998+00:00
-- url     : https://prove2.me/submissions/37df4f98-3f57-40ce-8810-b96bb71e3f5b

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
theorem _root_.solution (s : Set ℤ) (m : ℤ → BitVec W) : AgreeOutside s m m := Set.eqOn_refl m sᶜ
end AgreeOutside
end ThreeSumApsp.WordRam
