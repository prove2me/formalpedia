-- Prove2me | solution 1 for ThreeSumApsp.WordRam.step_accept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:10:36.923764+00:00
-- url     : https://prove2.me/submissions/14b0092b-7aaf-4658-90c4-c84af549baeb

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
theorem _root_.solution {c : Cfg W} (h : P.getD c.pc .reject = .accept) : step P c = .inr true := by
  simp only [step, h]
end ThreeSumApsp.WordRam
