-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.chosenDifference_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:58.318458+00:00
-- url     : https://prove2.me/submissions/839c7970-2011-40f5-9e35-1b4a0156e566

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_Word_frameDifference_ne_zero

set_option autoImplicit true
open Sabidussi
open Sabidussi.CyclicWord
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
open Sabidussi.CyclicWord.Word
variable (W : Word (V := V))
namespace Sabidussi.CyclicWord.Word
theorem _root_.solution
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) (i : W.Pos) :
    W.chosenDifference hmin choice i ≠ 0 := by
  exact W.frameDifference_ne_zero hmin _ _ _
end Sabidussi.CyclicWord.Word
