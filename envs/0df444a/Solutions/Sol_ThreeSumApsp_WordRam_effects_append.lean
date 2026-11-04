-- Prove2me | solution 1 for ThreeSumApsp.WordRam.effects_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:35.857293+00:00
-- url     : https://prove2.me/submissions/8a262d0c-1506-4362-80bb-ae8cf17ddd58

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
theorem _root_.solution (l₁ l₂ : List Instr) (m : ℤ → BitVec W) :
    effects (l₁ ++ l₂) m = effects l₂ (effects l₁ m) := by
  simp [effects, List.foldl_append]
end ThreeSumApsp.WordRam
