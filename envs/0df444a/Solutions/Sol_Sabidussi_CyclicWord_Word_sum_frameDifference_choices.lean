-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.sum_frameDifference_choices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:24.273031+00:00
-- url     : https://prove2.me/submissions/71ddc06a-3029-4c13-b75c-39c9ab766271

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_sum_localDifference_choices


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
    (v : V) (o : W.Occurrence v) :
    ∑ c, W.frameDifference hmin v c o = 0 := by
  exact sum_localDifference_choices _ _
end Sabidussi.CyclicWord.Word
