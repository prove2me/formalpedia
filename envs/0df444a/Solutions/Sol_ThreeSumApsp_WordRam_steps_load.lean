-- Prove2me | solution 1 for ThreeSumApsp.WordRam.steps_load
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:10:34.558291+00:00
-- url     : https://prove2.me/submissions/0a94fec2-0b97-4465-8875-486d7d431237

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
import Theorems.Thm_ThreeSumApsp_WordRam_CodeAt_head
import Theorems.Thm_ThreeSumApsp_WordRam_effects_nil
import Theorems.Thm_ThreeSumApsp_WordRam_effects_cons
import Theorems.Thm_ThreeSumApsp_WordRam_effect_load
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
private theorem steps_instr {rest : List Instr} {pos : ℕ} {i : Instr}
    (hcode : CodeAt P pos (i :: rest)) (hi : Straight i) (m : ℤ → BitVec W) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, effect i m⟩ :=
  Steps.one (step_straight hcode.head hi)
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
variable {m : ℤ → BitVec W} {i j k a b : ℤ}
namespace ThreeSumApsp.WordRam
theorem _root_.solution {rest : List Instr} {pos : ℕ} (hcode : CodeAt P pos (.load i j :: rest))
    (hj : m j = wd W a) (ha : InRange W a) :
    Steps P 1 ⟨pos, m⟩ ⟨pos + 1, Function.update m i (m a)⟩ :=
  effect_load i hj ha ▸ steps_instr hcode trivial m
end ThreeSumApsp.WordRam
