-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.orderedLetterInteraction_chosen_eq_interaction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:46.97266+00:00
-- url     : https://prove2.me/submissions/56001d46-ec64-4286-9972-1b341226160d

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
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
    (choice : V → Fin 3) {v u : V} (hvu : v ≠ u) :
    W.orderedLetterInteraction (W.chosenDifference hmin choice) v u =
      W.interaction hmin v u (choice v) (choice u) := by
  unfold orderedLetterInteraction interaction
  rw [if_neg hvu]
  apply Fintype.sum_congr
  intro i
  apply Fintype.sum_congr
  intro j
  rw [W.chosenDifference_at_occurrence hmin choice v i,
    W.chosenDifference_at_occurrence hmin choice u j]
end Sabidussi.CyclicWord.Word
