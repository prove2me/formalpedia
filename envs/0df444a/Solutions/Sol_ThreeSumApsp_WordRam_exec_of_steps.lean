-- Prove2me | solution 1 for ThreeSumApsp.WordRam.exec_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:10:32.042464+00:00
-- url     : https://prove2.me/submissions/0f84d0b5-a5b6-4c2d-a60d-2a6135ae6668

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Theorems.Thm_ThreeSumApsp_WordRam_exec_succ_of_verdict
import Theorems.Thm_ThreeSumApsp_WordRam_exec_succ_of_step

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
namespace ThreeSumApsp.WordRam
theorem _root_.solution {n : ℕ} {c c' : Cfg W} {v : Bool} (h : Steps P n c c')
    (hv : step P c' = .inr v) : exec P (n + 1) c.pc c.mem = some (v, c'.mem) := by
  induction n generalizing c with
  | zero =>
    obtain rfl := h
    exact exec_succ_of_verdict hv 0
  | succ n ih =>
    obtain ⟨c₁, hs, hr⟩ := h
    rw [exec_succ_of_step hs]
    exact ih hr
end ThreeSumApsp.WordRam
