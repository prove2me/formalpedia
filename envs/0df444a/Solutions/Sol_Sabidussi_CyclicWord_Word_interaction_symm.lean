-- Prove2me | solution 1 for Sabidussi.CyclicWord.Word.interaction_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:38.719982+00:00
-- url     : https://prove2.me/submissions/2d820592-2672-49ab-baa3-6ad05928b050

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_Word_sum_frameDifference_occurrences
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_comm
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_localDifference_one
import Theorems.Thm_Sabidussi_localDifference_zero
import Theorems.Thm_Sabidussi_sum_bracket_right
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
    (v u : V) (cv cu : Fin 3) :
    W.interaction hmin v u cv cu = W.interaction hmin u v cu cv := by
  by_cases hvu : v = u
  · subst u
    simp [interaction]
  · have hswap :
        (∑ i : W.Occurrence u, ∑ j : W.Occurrence v,
          if j.1 < i.1 then
            bracket (W.frameDifference hmin u cu i) (W.frameDifference hmin v cv j)
          else 0) =
        ∑ i : W.Occurrence v, ∑ j : W.Occurrence u,
          if i.1 < j.1 then
            bracket (W.frameDifference hmin u cu j) (W.frameDifference hmin v cv i)
          else 0 := by
      exact Finset.sum_comm
    have hsum :
        W.interaction hmin v u cv cu + W.interaction hmin u v cu cv = 0 := by
      simp only [interaction, if_neg hvu, if_neg (Ne.symm hvu)]
      rw [hswap, ← Finset.sum_add_distrib]
      simp_rw [← Finset.sum_add_distrib]
      calc
        (∑ i : W.Occurrence v, ∑ j : W.Occurrence u,
          ((if j.1 < i.1 then
              bracket (W.frameDifference hmin v cv i) (W.frameDifference hmin u cu j)
            else 0) +
           if i.1 < j.1 then
              bracket (W.frameDifference hmin u cu j) (W.frameDifference hmin v cv i)
            else 0)) =
            ∑ i : W.Occurrence v, ∑ j : W.Occurrence u,
              bracket (W.frameDifference hmin v cv i) (W.frameDifference hmin u cu j) := by
                apply Fintype.sum_congr
                intro i
                apply Fintype.sum_congr
                intro j
                have hij : i.1 ≠ j.1 := by
                  intro h
                  apply hvu
                  calc
                    v = W.letter i.1 := i.2.symm
                    _ = W.letter j.1 := congrArg W.letter h
                    _ = u := j.2
                rcases lt_trichotomy j.1 i.1 with hji | heq | hij'
                · simp [hji, not_lt_of_ge hji.le]
                · exact (hij heq.symm).elim
                · rw [if_neg (not_lt_of_ge hij'.le), if_pos hij', zero_add]
                  exact bracket_comm _ _
        _ = ∑ i : W.Occurrence v,
              bracket (W.frameDifference hmin v cv i)
                (∑ j : W.Occurrence u, W.frameDifference hmin u cu j) := by
              apply Fintype.sum_congr
              intro i
              exact sum_bracket_right _ _
        _ = 0 := by rw [W.sum_frameDifference_occurrences hmin u cu]; simp
    calc
      W.interaction hmin v u cv cu = W.interaction hmin v u cv cu + 0 := by simp
      _ = W.interaction hmin v u cv cu +
          (W.interaction hmin v u cv cu + W.interaction hmin u v cu cv) := by rw [hsum]
      _ = W.interaction hmin u v cu cv := by
        rw [← add_assoc, F₂_add_self, zero_add]
end Sabidussi.CyclicWord.Word
