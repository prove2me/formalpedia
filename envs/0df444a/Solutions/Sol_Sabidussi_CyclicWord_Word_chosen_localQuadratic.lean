-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.chosen_localQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:16:34.369262+00:00
-- url     : https://prove2.me/submissions/19051d90-87be-4ce3-a8e3-704c6210edc5

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_Word_frameDifference_localQuadratic
import Theorems.Thm_Sabidussi_CyclicWord_Word_chosenDifference_at_occurrence

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
    (choice : V → Fin 3) (v : V) :
    (∑ i : W.Occurrence v, quadratic (W.chosenDifference hmin choice i.1)) +
      W.orderedLetterInteraction (W.chosenDifference hmin choice) v v = 0 := by
  unfold orderedLetterInteraction
  simp_rw [W.chosenDifference_at_occurrence hmin choice v]
  exact W.frameDifference_localQuadratic hmin v (choice v)
end Sabidussi.CyclicWord.Word
