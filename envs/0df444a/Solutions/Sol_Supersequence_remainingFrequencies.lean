-- Prove2me | solution 1 for Supersequence.remainingFrequencies
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:12:09.3376+00:00
-- url     : https://prove2.me/submissions/af76ecaf-e980-4431-899b-5a6731a50ae1

import Definitions.Def_Frequency
import Definitions.Def_Four
import Theorems.Thm_Supersequence_noFour
import Theorems.Thm_Supersequence_frequencySplit


set_option autoImplicit true
open Supersequence
open List
variable {α : Type} [DecidableEq α]
namespace Supersequence
theorem _root_.solution {w : List (Fin 10)} (hw : Universal w) (len : w.length = 82)
    (f2 : LengthBound 2 3) (f3 : LengthBound 3 7) (f6 : LengthBound 6 28)
    (f7 : LengthBound 7 39) (f8 : LengthBound 8 52) (f9 : LengthBound 9 66)
    (x : Fin 10) (least : ∀ a, w.count x ≤ w.count a) :
    w.count x = 5 ∨ w.count x = 6 ∨ w.count x = 7 := by
  obtain ⟨lower,y,hy⟩ := frequencySplit f9 hw len
  have four := noFour hw len f2 f3 f6 f7 f8 f9 x
  have := least y
  have := lower x
  omega
end Supersequence
