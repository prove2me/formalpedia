-- Prove2me | solution 1 for ThreeSumApsp.WordRam.effect_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:43.490683+00:00
-- url     : https://prove2.me/submissions/475238c7-8faf-4748-87bf-23adaaf6d320

import Definitions.Def_Submission_EndStatement
import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_Submission_ThreeSumApsp_Machine_Steps
section
namespace ThreeSumApsp.WordRam
open EndStatement (Instr exec loadWords)
variable {W : ℕ} {P : List Instr}
private theorem wd_sub (a b : ℤ) : wd W a - wd W b = wd W (a - b) := by
  rw [sub_eq_add_neg a b, wd, wd, wd, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
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
theorem _root_.solution (i : ℤ) (hj : m j = wd W a) (hk : m k = wd W b) :
    effect (.sub i j k) m = Function.update m i (wd W (a - b)) := by
  rw [effect, hj, hk, wd_sub]
end ThreeSumApsp.WordRam
