-- Prove2me | solution 1 for ThreeSumApsp.WordRam.CodeAt.right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:02:22.055594+00:00
-- url     : https://prove2.me/submissions/746a1da1-38af-47f3-b46f-c6986b75e59a

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
theorem _root_.solution {pos : ℕ} {l₁ l₂ : List Instr} (h : CodeAt P pos (l₁ ++ l₂)) :
    CodeAt P (pos + l₁.length) l₂ := by
  obtain ⟨r, hr⟩ := h
  refine ⟨r, ?_⟩
  rw [← List.drop_drop, ← hr, List.append_assoc, List.drop_left]
end CodeAt
end ThreeSumApsp.WordRam
