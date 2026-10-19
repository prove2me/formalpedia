-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.secondMultiplicity_diagonalImage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/2127d107-a5f8-431c-bd9a-d6faf6ca618d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_secondFiber_diagonalImage

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) (x : V) :
    secondMultiplicity (diagonalImage p U) (p x) =
      secondMultiplicity U x := by
  unfold secondMultiplicity
  rw [secondFiber_diagonalImage]
  exact Finset.card_image_of_injective _ (p.prodCongr p).injective
end SoficGroups.KunThomFiberCoarea
