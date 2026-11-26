-- Prove2me | solution 1 for Sabidussi.OddBalance.Derangement.inv_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:13.596447+00:00
-- url     : https://prove2.me/submissions/08dd8a15-7ba6-4aa1-8b31-02eaff8e51fa

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
namespace Derangement
theorem _root_.solution {S : Finset V} (d : Derangement S) : d.inv.inv = d := by
  apply Subtype.ext
  exact d.1.symm_symm
end Derangement
end Sabidussi.OddBalance
