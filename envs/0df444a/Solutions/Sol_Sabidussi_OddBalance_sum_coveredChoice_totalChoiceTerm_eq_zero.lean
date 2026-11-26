-- Prove2me | solution 1 for Sabidussi.OddBalance.sum_coveredChoice_totalChoiceTerm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:14:53.332366+00:00
-- url     : https://prove2.me/submissions/bd32104a-092c-41d8-af5d-61d09ba27bc4

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_sum_derangement_totalChoiceTerm_eq_zero

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
    (∑ c : CoveredChoice S, totalChoiceTerm b S c.1) = 0 := by
  calc
    (∑ c : CoveredChoice S, totalChoiceTerm b S c.1) =
        ∑ d : Derangement S, totalChoiceTerm b S d.choice := by
          apply Fintype.sum_equiv (coveredChoiceEquivDerangement S)
          intro c
          change totalChoiceTerm b S c.1 =
            totalChoiceTerm b S c.toDerangement.choice
          exact congrArg (totalChoiceTerm b S)
            (CoveredChoice.toDerangement_choice c).symm
    _ = 0 := sum_derangement_totalChoiceTerm_eq_zero b hsymm hrow S hS
end Sabidussi.OddBalance
