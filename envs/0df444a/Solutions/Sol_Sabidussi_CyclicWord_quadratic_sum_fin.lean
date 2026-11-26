-- Prove2me | solution 1 for Sabidussi.CyclicWord.quadratic_sum_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:20.774208+00:00
-- url     : https://prove2.me/submissions/6ebbe101-f60c-487a-a053-313093561160

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_comm
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_localDifference_one
import Theorems.Thm_Sabidussi_localDifference_zero
import Theorems.Thm_Sabidussi_quadratic_add
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


section
namespace Sabidussi
namespace CyclicWord
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Word
variable (W : Word (V := V))
end Word
section LocalPattern
private theorem orderedPairSum_succ (k : ℕ) (f : Fin (k + 1) → Color) :
    (∑ i, ∑ j, if j < i then bracket (f i) (f j) else 0) =
      (∑ i : Fin k, ∑ j : Fin k,
        if j < i then bracket (f i.castSucc) (f j.castSucc) else 0) +
      ∑ j : Fin k, bracket (f (Fin.last k)) (f j.castSucc) := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Fintype.sum_congr
    intro i
    rw [Fin.sum_univ_castSucc]
    rw [if_neg (not_lt_of_ge (Fin.castSucc_lt_last i).le)]
    simp
  · rw [Fin.sum_univ_castSucc]
    simp
end LocalPattern
namespace Word
section Frames
variable (W : Word (V := V))
end Frames
section Interaction
variable (W : Word (V := V))
end Interaction
section DifferencesAndPrefixes
variable (W : Word (V := V))
end DifferencesAndPrefixes
end Word
end CyclicWord
end Sabidussi
end

set_option autoImplicit true
open Sabidussi
open Sabidussi.CyclicWord
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Sabidussi.CyclicWord
theorem _root_.solution (k : ℕ) (f : Fin k → Color) :
    quadratic (∑ i, f i) =
      (∑ i, quadratic (f i)) +
        ∑ i, ∑ j, if j < i then bracket (f i) (f j) else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc, quadratic_add, ih (fun i ↦ f i.castSucc),
        Fin.sum_univ_castSucc, orderedPairSum_succ]
      rw [bracket_comm, ← sum_bracket_right]
      abel
end Sabidussi.CyclicWord
