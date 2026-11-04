-- Prove2me | solution 1 for ThreeSumApsp.WordRam.CodeAt.head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:34.747233+00:00
-- url     : https://prove2.me/submissions/1fcc13cb-f549-4337-98b3-613b9b91f34d

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
namespace CodeAt
theorem _root_.solution {pos : ℕ} {i : Instr} {l : List Instr} (h : CodeAt P pos (i :: l)) :
    P.getD pos .reject = i := by
  obtain ⟨r, hr⟩ := h
  have : (P.drop pos)[0]? = some i := by rw [← hr]; rfl
  rw [List.getElem?_drop, Nat.add_zero] at this
  rw [List.getD_eq_getElem?_getD, this]
  rfl
end CodeAt
end ThreeSumApsp.WordRam
