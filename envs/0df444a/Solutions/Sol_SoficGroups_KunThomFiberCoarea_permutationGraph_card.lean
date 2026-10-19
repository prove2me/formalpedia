-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.permutationGraph_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/f49b64c5-1876-4414-b3f6-c54d82645b35

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : Equiv.Perm V) :
    (SoficGroups.permutationGraph p).card = Fintype.card V := by
  classical
  have hinj : Function.Injective (fun x : V => (x, p x)) := by
    intro x y h
    exact congrArg Prod.fst h
  simpa [SoficGroups.permutationGraph] using
    (Finset.card_image_of_injective Finset.univ hinj)
end SoficGroups.KunThomFiberCoarea
