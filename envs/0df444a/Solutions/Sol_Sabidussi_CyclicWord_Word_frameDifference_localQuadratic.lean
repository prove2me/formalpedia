-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.frameDifference_localQuadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:15:05.255698+00:00
-- url     : https://prove2.me/submissions/5f841497-78e1-44dd-90b4-3c8edafb4c14

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_localQuadraticContribution_eq_zero
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
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) (v : V) (c : Fin 3) :
    (∑ o, quadratic (W.frameDifference hmin v c o)) +
      (∑ o, ∑ p,
        if p.1 < o.1 then
          bracket (W.frameDifference hmin v c o) (W.frameDifference hmin v c p)
        else 0) = 0 := by
  let k := Fintype.card (W.Occurrence v) - 2
  let e := W.occurrenceOrderIsoFin hmin v
  change (∑ o, quadratic (localDifference k c (e o))) +
      (∑ o, ∑ p,
        if p.1 < o.1 then bracket (localDifference k c (e o)) (localDifference k c (e p))
        else 0) = 0
  have hq :
      (∑ o, quadratic (localDifference k c (e o))) =
        ∑ i : Fin (k + 2), quadratic (localDifference k c i) := by
    apply Fintype.sum_equiv e.toEquiv
    intro o
    rfl
  rw [hq]
  have hpairs :
      (∑ o, ∑ p,
        if p.1 < o.1 then bracket (localDifference k c (e o)) (localDifference k c (e p))
        else 0) =
      ∑ i : Fin (k + 2), ∑ j : Fin (k + 2),
        if j < i then bracket (localDifference k c i) (localDifference k c j) else 0 := by
    apply Fintype.sum_equiv e.toEquiv
    intro o
    apply Fintype.sum_equiv e.toEquiv
    intro p
    change (if p < o then _ else _) = (if e p < e o then _ else _)
    by_cases hpo : p < o
    · simp [hpo, (e.lt_iff_lt).mpr hpo]
    · have he : ¬ e p < e o := by simpa using hpo
      simp [hpo, he]
  rw [hpairs]
  exact localQuadraticContribution_eq_zero k c
end Sabidussi.CyclicWord.Word
