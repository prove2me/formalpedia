-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.firstMultiplicity_diagonalImage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/29ee249b-25bd-4f21-ac90-835c4afe8794

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_firstFiber_diagonalImage

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) (x : V) :
    firstMultiplicity (diagonalImage p U) (p x) =
      firstMultiplicity U x := by
  unfold firstMultiplicity
  rw [firstFiber_diagonalImage]
  exact Finset.card_image_of_injective _ (p.prodCongr p).injective
end SoficGroups.KunThomFiberCoarea
