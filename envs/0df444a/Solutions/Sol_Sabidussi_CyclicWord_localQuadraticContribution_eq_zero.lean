-- Prove2me | solution 1 for Sabidussi.CyclicWord.localQuadraticContribution_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:14:18.886017+00:00
-- url     : https://prove2.me/submissions/02ae996c-7b89-4b5d-96b5-25762a3aeb7b

import Definitions.Def_Sabidussi_LocalPattern
import Definitions.Def_Sabidussi_OddBalance
import Definitions.Def_Sabidussi_Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin
import Definitions.Def_Sabidussi_CyclicWord
import Theorems.Thm_Sabidussi_CyclicWord_quadratic_sum_fin
import Theorems.Thm_Sabidussi_quadratic_sum_fin
import Theorems.Thm_Sabidussi_sum_localDifference_occurrences


set_option autoImplicit true
open Sabidussi
open Sabidussi.CyclicWord
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Sabidussi.CyclicWord
theorem _root_.solution (n : ℕ) (c : Fin 3) :
    localQuadraticContribution n c = 0 := by
  unfold localQuadraticContribution
  rw [← quadratic_sum_fin]
  rw [sum_localDifference_occurrences]
  rfl
end Sabidussi.CyclicWord
