-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.incident_sum_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:15:01.199139+00:00
-- url     : https://prove2.me/submissions/0e9732c5-92ca-4918-b18d-d538294e8429

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_Word_sum_chosenDifference_occurrences
import Theorems.Thm_Sabidussi_CyclicWord_Word_sum_chosenDifference
import Theorems.Thm_Sabidussi_CyclicWord_Word_prefixColor_transition
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_localDifference_one
import Theorems.Thm_Sabidussi_localDifference_zero
import Theorems.Thm_Sabidussi_tripleDifference_one
import Theorems.Thm_Sabidussi_tripleDifference_two
import Theorems.Thm_Sabidussi_tripleDifference_zero
attribute [local simp] Sabidussi.bracketRightHom_apply
attribute [local simp] Sabidussi.bracket_self
attribute [local simp] Sabidussi.localDifference_one
attribute [local simp] Sabidussi.localDifference_zero
attribute [local simp] Sabidussi.tripleDifference_one
attribute [local simp] Sabidussi.tripleDifference_two
attribute [local simp] Sabidussi.tripleDifference_zero



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
    let y := W.chosenDifference hmin choice
    let x := W.prefixColor y
    ∑ os : W.Occurrence v × Fin 2, W.incidentColor x os.1 os.2 = 0 := by
  dsimp only
  let y := W.chosenDifference hmin choice
  let x := W.prefixColor y
  have htotal : ∑ i, y i = 0 := W.sum_chosenDifference hmin choice
  calc
    (∑ os : W.Occurrence v × Fin 2, W.incidentColor x os.1 os.2) =
        ∑ i : W.Occurrence v, (x (W.prev i.1) + x i.1) := by
          rw [Fintype.sum_prod_type]
          apply Fintype.sum_congr
          intro i
          rw [Fin.sum_univ_two]
          rfl
    _ = ∑ i : W.Occurrence v, y i.1 := by
          apply Fintype.sum_congr
          intro i
          exact W.prefixColor_transition y htotal i.1
    _ = 0 := W.sum_chosenDifference_occurrences hmin choice v
end Sabidussi.CyclicWord.Word
