-- Prove2me | solution 1 for Sabidussi.OddBalance.sum_obstruction_product_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:16:16.672859+00:00
-- url     : https://prove2.me/submissions/8550d827-749a-46cd-9049-462e34499188

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_sum_obstruction_product_expand
import Theorems.Thm_Sabidussi_OddBalance_sum_choice_totalChoiceTerm_eq_zero

set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Sabidussi.OddBalance
theorem _root_.solution
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0)
    (S : Finset V) (hS : S.Nonempty) :
    (∑ x : V → Fin 3, ∏ v ∈ S, obstruction b x v) = 0 := by
  rw [sum_obstruction_product_expand]
  exact sum_choice_totalChoiceTerm_eq_zero b hsymm hrow S hS
end Sabidussi.OddBalance
