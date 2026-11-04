-- Prove2me | solution 1 for ThreeSumApsp.WordRam.steps_bltz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:09:45.732283+00:00
-- url     : https://prove2.me/submissions/7f21f828-34a9-47aa-a60e-fa57bf592019

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Theorems.Thm_ThreeSumApsp_WordRam_toInt_wd
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_head
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
theorem _root_.solution {rest : List Instr} {pos l : ℕ} {c v : ℤ} {m : ℤ → BitVec W}
    (hcode : CodeAt P pos (.bltz c l :: rest)) (hc : m c = wd W v) (hv : InRange W v) :
    Steps P 1 ⟨pos, m⟩ ⟨if v < 0 then l else pos + 1, m⟩ := by
  refine Steps.one ?_
  simp only [step, hcode.head, hc, toInt_wd hv]
end ThreeSumApsp.WordRam
