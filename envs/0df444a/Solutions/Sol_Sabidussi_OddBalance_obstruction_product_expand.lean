-- Prove2me | solution 1 for Sabidussi.OddBalance.obstruction_product_expand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:40.134799+00:00
-- url     : https://prove2.me/submissions/46ac58b9-eb5d-4c88-a57a-1426a7f82932

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
theorem _root_.solution
    (b : V → V → Fin 3 → Fin 3 → F2) (S : Finset V) (x : V → Fin 3) :
    (∏ v ∈ S, obstruction b x v) =
      ∑ f : Choice S, choiceTerm b S f x := by
  rw [Finset.prod_subtype S (fun _ => Iff.rfl)]
  have hsum (v : V) :
      (∑ u ∈ Finset.univ.erase v, b v u (x v) (x u)) =
        ∑ u : {u : V // u ≠ v}, b v u (x v) (x u) := by
    exact Finset.sum_subtype (Finset.univ.erase v) (by simp)
      (fun u => b v u (x v) (x u))
  simp_rw [obstruction, hsum]
  exact Fintype.prod_sum (fun v : {v // v ∈ S} =>
    fun u : {u : V // u ≠ v} => b v u (x v) (x u))
end Sabidussi.OddBalance
