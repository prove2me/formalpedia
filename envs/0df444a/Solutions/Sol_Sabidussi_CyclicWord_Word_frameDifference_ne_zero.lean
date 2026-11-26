-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.frameDifference_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:21.321788+00:00
-- url     : https://prove2.me/submissions/0b1b0df3-9e89-4a7b-8006-3c63c9ad604b

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_localDifference_ne_zero


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
    (v : V) (c : Fin 3) (o : W.Occurrence v) :
    W.frameDifference hmin v c o ≠ 0 := by
  exact localDifference_ne_zero _ _ _
end Sabidussi.CyclicWord.Word
