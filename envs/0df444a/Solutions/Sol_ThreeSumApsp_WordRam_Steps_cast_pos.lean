-- Prove2me | solution 1 for ThreeSumApsp.WordRam.Steps.cast_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:07:46.336367+00:00
-- url     : https://prove2.me/submissions/1e211b43-1a94-49d0-b2b8-34052e8e558c

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
namespace Steps
theorem _root_.solution {n p p' : ℕ} {c : Cfg W} {m : ℤ → BitVec W} (h : Steps P n c ⟨p, m⟩)
    (hp : p = p') : Steps P n c ⟨p', m⟩ := hp ▸ h
end Steps
end ThreeSumApsp.WordRam
