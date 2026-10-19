-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.diagonalImage_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/2a4f8680-40a7-470b-818f-d4eac624b794

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) :
    (diagonalImage p U).card = U.card := by
  exact Finset.card_image_of_injective U (p.prodCongr p).injective
end SoficGroups.KunThomFiberCoarea
