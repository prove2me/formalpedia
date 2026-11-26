-- Prove2me | solution 1 for Sabidussi.OddBalance.prod_sum_expand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:15:54.846815+00:00
-- url     : https://prove2.me/submissions/328578c5-9844-46af-be8d-71a76964ed69

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
theorem _root_.solution (S : Finset V) (t : V → Finset V) (a : V → V → F2) :
    (∏ v ∈ S, ∑ u ∈ t v, a v u) =
      ∑ f : (v : {v // v ∈ S}) → {u // u ∈ t v},
        ∏ v : {v // v ∈ S}, a v (f v) := by
  rw [Finset.prod_subtype S (fun _ => Iff.rfl)]
  simp_rw [Finset.sum_subtype (t _) (fun _ => Iff.rfl)]
  exact Fintype.prod_sum (fun v : {v // v ∈ S} =>
    fun u : {u // u ∈ t v} => a v u)
end Sabidussi.OddBalance
