-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.exists_coloring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:19:20.506658+00:00
-- url     : https://prove2.me/submissions/fbb5d8e4-5ac5-4dee-ade3-51e221134069

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_Word_exists_balanced_choice
import Theorems.Thm_Sabidussi_CyclicWord_Word_chosenDifference_ne_zero
import Theorems.Thm_Sabidussi_CyclicWord_Word_sum_chosenDifference
import Theorems.Thm_Sabidussi_CyclicWord_Word_prefixColor_transition
import Theorems.Thm_Sabidussi_CyclicWord_Word_quadratic_incident_sum_eq_zero
import Theorems.Thm_Sabidussi_CyclicWord_Word_incident_sum_eq_zero
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_colorFiber_card_even_of_moments
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
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) : Nonempty W.Coloring := by
  obtain ⟨choice, hbalanced⟩ := W.exists_balanced_choice hmin
  let y := W.chosenDifference hmin choice
  let x := W.prefixColor y
  have htotal : ∑ i, y i = 0 := W.sum_chosenDifference hmin choice
  refine ⟨{
    color := x
    transition_ne := ?_
    color_even := ?_ }⟩
  · intro i hxeq
    apply W.chosenDifference_ne_zero hmin choice i
    calc
      y i = x (W.prev i) + x i := (W.prefixColor_transition y htotal i).symm
      _ = 0 := by rw [hxeq, color_add_self]
  · intro v z
    let f : W.Occurrence v × Fin 2 → Color :=
      fun os ↦ W.incidentColor x os.1 os.2
    have hcard : Even (Fintype.card (W.Occurrence v × Fin 2)) := by
      rw [Fintype.card_prod, Fintype.card_fin]
      exact ⟨Fintype.card (W.Occurrence v), by omega⟩
    have hsum : ∑ os, f os = 0 := W.incident_sum_eq_zero hmin choice v
    have hquad : ∑ os, quadratic (f os) = 0 :=
      W.quadratic_incident_sum_eq_zero hmin choice hbalanced v
    have heven := colorFiber_card_even_of_moments f hcard hsum hquad z
    rw [Fintype.card_subtype]
    simpa [colorFiber, f] using heven
end Sabidussi.CyclicWord.Word
