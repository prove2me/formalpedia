-- Prove2me | solution 1 for Sabidussi.OddBalance.prod_one_add_expand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:28.240838+00:00
-- url     : https://prove2.me/submissions/7947a2fc-3b7f-4ce3-a00f-60cc16e7d371

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance

set_option autoImplicit true
open scoped BigOperators
open Finset
open Sabidussi
open Sabidussi.OddBalance
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace Sabidussi.OddBalance
theorem _root_.solution (q : V → F2) :
    (∏ v : V, (1 + q v)) =
      ∑ S ∈ Finset.univ.powerset, ∏ v ∈ S, q v := by
  simpa [add_comm] using Finset.prod_add q (fun _ : V => (1 : F2)) Finset.univ
end Sabidussi.OddBalance
