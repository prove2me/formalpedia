-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.exists_balanced_choice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:18:36.096617+00:00
-- url     : https://prove2.me/submissions/ac86a6f3-ead5-44c7-a48b-99d21c87a59d

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_Word_interaction_symm
import Theorems.Thm_Sabidussi_CyclicWord_Word_sum_interaction_choices
import Theorems.Thm_Sabidussi_OddBalance_exists_balanced


set_option autoImplicit true
open Sabidussi
open Sabidussi.CyclicWord
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
open Sabidussi.CyclicWord.Word
variable (W : Word (V := V))
namespace Sabidussi.CyclicWord.Word
theorem _root_.solution
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) :
    ∃ choice : V → Fin 3,
      ∀ v, OddBalance.obstruction (W.interaction hmin) choice v = 0 := by
  exact OddBalance.exists_balanced (W.interaction hmin)
    (W.interaction_symm hmin) (W.sum_interaction_choices hmin)
end Sabidussi.CyclicWord.Word
