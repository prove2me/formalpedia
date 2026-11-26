-- Prove2me | solution 1 for Sabidussi.OddBalance.sum_derangement_totalChoiceTerm_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:14:16.27153+00:00
-- url     : https://prove2.me/submissions/fdde710e-b942-4716-8e8a-4c7aa71894df

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Equiv.Prod
import Definitions.Def_Sabidussi_OddBalance
import Theorems.Thm_Sabidussi_OddBalance_F2_add_self
import Theorems.Thm_Sabidussi_OddBalance_Derangement_inv_inv
import Theorems.Thm_Sabidussi_OddBalance_totalChoiceTerm_derangement_inv
import Theorems.Thm_Sabidussi_OddBalance_totalChoiceTerm_eq_zero_of_derangement_inv_eq_self

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
    (∑ d : Derangement S, totalChoiceTerm b S d.choice) = 0 := by
  classical
  apply Finset.sum_involution (s := Finset.univ)
    (f := fun d : Derangement S => totalChoiceTerm b S d.choice)
    (g := fun d _ => d.inv)
  · intro d _
    rw [totalChoiceTerm_derangement_inv b hsymm S d]
    exact F2.add_self _
  · intro d _ hdne hinv
    apply hdne
    exact totalChoiceTerm_eq_zero_of_derangement_inv_eq_self
      b hsymm hrow S hS d hinv
  · simp
  · intro d _
    exact Derangement.inv_inv d
end Sabidussi.OddBalance
