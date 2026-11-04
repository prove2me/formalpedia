-- Prove2me | solution 1 for ThreeSumApsp.WordRam.step_reject
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:10:38.245237+00:00
-- url     : https://prove2.me/submissions/f4e46068-0d4c-4f89-a493-bbeefd41d413

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
namespace ThreeSumApsp.WordRam
theorem _root_.solution {c : Cfg W} (h : P.getD c.pc .reject = .reject) : step P c = .inr false := by
  simp only [step, h]
end ThreeSumApsp.WordRam
