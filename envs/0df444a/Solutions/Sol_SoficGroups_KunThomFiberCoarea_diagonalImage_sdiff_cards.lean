-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.diagonalImage_sdiff_cards
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/9d826fec-55a2-4955-b9ec-c6472035ca5e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_diagonalImage_card
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_diagonalImage_sdiff_eq_image_exit

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution {V : Type*} [DecidableEq V]
    (p : Equiv.Perm V) (U : Finset (V × V)) :
    (diagonalImage p U \ U).card = diagonalExit p U ∧
      (U \ diagonalImage p U).card = diagonalExit p U := by
  have hforward : (diagonalImage p U \ U).card = diagonalExit p U := by
    rw [diagonalImage_sdiff_eq_image_exit]
    exact Finset.card_image_of_injective _ (p.prodCongr p).injective
  have hU := Finset.card_sdiff_add_card_inter U (diagonalImage p U)
  have hI := Finset.card_sdiff_add_card_inter (diagonalImage p U) U
  have hinter : (U ∩ diagonalImage p U).card =
      (diagonalImage p U ∩ U).card := by
    rw [Finset.inter_comm]
  have hcard := diagonalImage_card p U
  exact ⟨hforward, by omega⟩
end SoficGroups.KunThomFiberCoarea
