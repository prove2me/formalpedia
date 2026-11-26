-- Prove2me | solution 1 for Sabidussi.OddBalance.totalChoiceTerm_derangement_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:41.419749+00:00
-- url     : https://prove2.me/submissions/cf68d992-942b-426c-8d13-ee918813d3eb

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_choiceTerm_derangement_inv

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
    (S : Finset V) (d : Derangement S) :
    totalChoiceTerm b S d.inv.choice = totalChoiceTerm b S d.choice := by
  apply Fintype.sum_congr
  intro x
  exact choiceTerm_derangement_inv b hsymm S d x
end Sabidussi.OddBalance
