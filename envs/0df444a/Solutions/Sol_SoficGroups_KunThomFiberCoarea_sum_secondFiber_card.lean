-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.sum_secondFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/c6fb8eeb-ac51-453d-8ad9-b6b46ba2ba18

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (∑ x : V, (secondFiber U x).card) = U.card := by
  classical
  simpa [secondFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (f := Prod.snd) (s := U) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm
end SoficGroups.KunThomFiberCoarea
