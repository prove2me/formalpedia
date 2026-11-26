-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.sum_chosenDifference_occurrences
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:35.959051+00:00
-- url     : https://prove2.me/submissions/fc667fc9-04f1-41ac-a0dc-7c0e2f8b96df

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_Word_sum_frameDifference_occurrences

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
    ∑ o : W.Occurrence v, W.chosenDifference hmin choice o.1 = 0 := by
  calc
    (∑ o : W.Occurrence v, W.chosenDifference hmin choice o.1) =
        ∑ o : W.Occurrence v, W.frameDifference hmin v (choice v) o := by
          apply Fintype.sum_congr
          rintro ⟨i, hi⟩
          subst v
          rfl
    _ = 0 := W.sum_frameDifference_occurrences hmin v (choice v)
end Sabidussi.CyclicWord.Word
