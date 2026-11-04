-- Prove2me | solution 1 for ThreeSumApsp.WordRam.effect_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:10:33.238949+00:00
-- url     : https://prove2.me/submissions/ffc182cc-9009-4a49-9a23-4a17768dbbfa

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
private theorem wd_mul (a b : ℤ) : wd W a * wd W b = wd W (a * b) := (BitVec.ofInt_mul a b).symm
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
    effect (.mul i j k) m = Function.update m i (wd W (a * b)) := by
  rw [effect, hj, hk, wd_mul]
end ThreeSumApsp.WordRam
