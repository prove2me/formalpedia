-- Prove2me | solution 1 for ThreeSumApsp.WordRam.agreeOutside_effects
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:13:43.544319+00:00
-- url     : https://prove2.me/submissions/23edf489-2800-4075-9b7b-0dabd7463bea

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_refl
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_refl
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_update
section
namespace ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
section known
variable {m : ℤ → BitVec W} {i j k a b : ℤ}
end known
section framing
variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}
private theorem agreeOutside_effect {i : Instr} (h : WritesIn s i) (m : ℤ → BitVec W) :
    AgreeOutside s m (effect i m) := by
  cases i <;>
    first | exact (AgreeOutside.refl s m).update h _ | exact AgreeOutside.refl s m | exact h.elim
end framing
end ThreeSumApsp.WordRam
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}
namespace ThreeSumApsp.WordRam
theorem _root_.solution {l : List Instr} (h : ∀ i ∈ l, WritesIn s i) (m : ℤ → BitVec W) :
    AgreeOutside s m (effects l m) := by
  induction l generalizing m with
  | nil => exact AgreeOutside.refl s m
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 h
    exact (agreeOutside_effect hi m).trans (ih hl _)
end ThreeSumApsp.WordRam
