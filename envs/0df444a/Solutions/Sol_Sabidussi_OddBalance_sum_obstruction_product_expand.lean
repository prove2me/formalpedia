-- Prove2me | solution 1 for Sabidussi.OddBalance.sum_obstruction_product_expand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:06.098579+00:00
-- url     : https://prove2.me/submissions/e22a63d6-4082-42ee-87f0-9493d939fa13

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_obstruction_product_expand

set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Sabidussi.OddBalance
theorem _root_.solution
    (b : V → V → Fin 3 → Fin 3 → F2) (S : Finset V) :
    (∑ x : V → Fin 3, ∏ v ∈ S, obstruction b x v) =
      ∑ f : Choice S, totalChoiceTerm b S f := by
  simp_rw [obstruction_product_expand]
  exact Finset.sum_comm
end Sabidussi.OddBalance
