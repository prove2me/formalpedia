-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.chosen_externalInteraction_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:14:33.794896+00:00
-- url     : https://prove2.me/submissions/efc0a3d8-91c0-4718-ae25-95943de08a35

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_Word_orderedLetterInteraction_chosen_eq_interaction

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
    (choice : V → Fin 3)
    (hbalanced : ∀ v, OddBalance.obstruction (W.interaction hmin) choice v = 0)
    (v : V) :
    ∑ u ∈ Finset.univ.erase v,
      W.orderedLetterInteraction (W.chosenDifference hmin choice) v u = 0 := by
  calc
    (∑ u ∈ Finset.univ.erase v,
      W.orderedLetterInteraction (W.chosenDifference hmin choice) v u) =
        ∑ u ∈ Finset.univ.erase v,
          W.interaction hmin v u (choice v) (choice u) := by
            apply Finset.sum_congr rfl
            intro u hu
            exact W.orderedLetterInteraction_chosen_eq_interaction hmin choice
              (Ne.symm (Finset.mem_erase.mp hu).1)
    _ = OddBalance.obstruction (W.interaction hmin) choice v := rfl
    _ = 0 := hbalanced v
end Sabidussi.CyclicWord.Word
