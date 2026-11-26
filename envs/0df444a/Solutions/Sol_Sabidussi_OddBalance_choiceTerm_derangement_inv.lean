-- Prove2me | solution 1 for Sabidussi.OddBalance.choiceTerm_derangement_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:13:17.441788+00:00
-- url     : https://prove2.me/submissions/9e896c0e-92e6-4d70-816d-f3ceff177b03

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
    (b : V → V → Fin 3 → Fin 3 → F2)
    (hsymm : ∀ v u a c, b v u a c = b u v c a)
    (S : Finset V) (d : Derangement S) (x : V → Fin 3) :
    choiceTerm b S d.inv.choice x = choiceTerm b S d.choice x := by
  rw [choiceTerm, choiceTerm]
  calc
    (∏ v : {v // v ∈ S},
        b v (d.inv.choice v) (x v) (x (d.inv.choice v))) =
        ∏ v : {v // v ∈ S},
          b (d.1.symm v) v (x (d.1.symm v)) (x v) := by
            apply Fintype.prod_congr
            intro v
            exact hsymm _ _ _ _
    _ = ∏ v : {v // v ∈ S}, b v (d.choice v) (x v) (x (d.choice v)) := by
      simpa [Derangement.choice, Derangement.inv] using
        (d.1.symm.prod_comp (fun v : {v // v ∈ S} =>
          b v (d.1 v) (x v) (x (d.1 v))))
end Sabidussi.OddBalance
