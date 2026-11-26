-- Prove2me | solution 1 for Sabidussi.OddBalance.cast_solutions_card_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:16:40.631598+00:00
-- url     : https://prove2.me/submissions/c84c9231-1e83-4dd7-9fb6-cfe033b5232e

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_cast_solutions_card
import Theorems.Thm_Sabidussi_OddBalance_sum_prod_one_add_expand
import Theorems.Thm_Sabidussi_OddBalance_sum_obstruction_product_eq_zero
import Theorems.Thm_Sabidussi_OddBalance_sum_one_fin3_assignments

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
    (hrow : ∀ v u a, ∑ c : Fin 3, b v u a c = 0) :
    ((solutions b).card : F2) = 1 := by
  rw [cast_solutions_card]
  rw [sum_prod_one_add_expand]
  rw [Finset.sum_eq_single ∅]
  · simpa using (sum_one_fin3_assignments (V := V))
  · intro S hSpow hSne
    apply sum_obstruction_product_eq_zero b hsymm hrow S
    simpa only [Finset.nonempty_iff_ne_empty] using hSne
  · simp
end Sabidussi.OddBalance
