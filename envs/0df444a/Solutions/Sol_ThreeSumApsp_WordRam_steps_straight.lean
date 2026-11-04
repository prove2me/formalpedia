-- Prove2me | solution 1 for ThreeSumApsp.WordRam.steps_straight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:13:17.473195+00:00
-- url     : https://prove2.me/submissions/0da28310-bdbd-480f-89ad-f64c74acb54f

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_head
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_tail
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_cast_pos
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
attribute [local simp] ThreeSumApsp.WordRam.effects_nil
attribute [local simp] ThreeSumApsp.WordRam.effects_cons
section
namespace ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
private theorem wd_one : (1 : BitVec W) = wd W 1 := BitVec.eq_of_toNat_eq rfl
private theorem step_straight {c : Cfg W} {i : Instr} (h : P.getD c.pc .reject = i)
    (hi : Straight i) : step P c = .inl ⟨c.pc + 1, effect i c.mem⟩ := by
  have write (a : ℤ) (v : BitVec W) :
      (fun x => if x = a then v else c.mem x) = Function.update c.mem a v := by
    funext x
    simp [Function.update_apply]
  cases i <;> simp only [Straight] at hi <;> simp only [step, h, effect, write, wd_one]
section known
variable {m : ℤ → BitVec W} {i j k a b : ℤ}
end known
section framing
variable {s t : Set ℤ} {m m' m₁ m₂ m₃ : ℤ → BitVec W} {a : ℤ}
end framing
end ThreeSumApsp.WordRam
set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
namespace ThreeSumApsp.WordRam
theorem _root_.solution (l : List Instr) (pc : ℕ) (m : ℤ → BitVec W) (hcode : CodeAt P pc l)
    (hl : ∀ i ∈ l, Straight i) : Steps P l.length ⟨pc, m⟩ ⟨pc + l.length, effects l m⟩ := by
  induction l generalizing pc m with
  | nil => rfl
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.forall_mem_cons.1 hl
    exact ⟨_, step_straight hcode.head hi,
      (ih (pc + 1) (effect i m) hcode.tail hl).cast_pos (by rw [List.length_cons]; omega)⟩
end ThreeSumApsp.WordRam
