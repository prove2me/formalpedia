-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.sum_firstFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/786f31c4-2f47-4301-989b-aaf8dee28e4d

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset (V × V)) :
    (∑ x : V, (firstFiber U x).card) = U.card := by
  classical
  simpa [firstFiber] using
    (Finset.card_eq_sum_card_fiberwise
      (f := Prod.fst) (s := U) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm
end SoficGroups.KunThomFiberCoarea
