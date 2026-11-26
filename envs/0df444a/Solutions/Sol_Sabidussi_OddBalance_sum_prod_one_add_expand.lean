-- Prove2me | solution 1 for Sabidussi.OddBalance.sum_prod_one_add_expand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:55.380835+00:00
-- url     : https://prove2.me/submissions/d8c1148d-3769-429e-9043-5be4d40e39ac

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_prod_one_add_expand

set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Sabidussi.OddBalance
theorem _root_.solution (q : (V → Fin 3) → V → F2) :
    (∑ x : V → Fin 3, ∏ v : V, (1 + q x v)) =
      ∑ S ∈ Finset.univ.powerset, ∑ x : V → Fin 3, ∏ v ∈ S, q x v := by
  simp_rw [prod_one_add_expand]
  exact Finset.sum_comm
end Sabidussi.OddBalance
