-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.chosenDifference_at_occurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:22.264143+00:00
-- url     : https://prove2.me/submissions/70cd2b0d-ed8a-419d-8cc4-d0f1f0cc7c5f

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord

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
    (choice : V → Fin 3) (v : V) (o : W.Occurrence v) :
    W.chosenDifference hmin choice o.1 = W.frameDifference hmin v (choice v) o := by
  rcases o with ⟨i, hi⟩
  subst v
  rfl
end Sabidussi.CyclicWord.Word
