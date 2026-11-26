-- Prove2me | solution 1 for Sabidussi.cast_colorFiber_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:11:29.979452+00:00
-- url     : https://prove2.me/submissions/579773fe-c445-4e43-a464-7fbfd8773bd5

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Parity
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_tripleDifference_one
import Theorems.Thm_Sabidussi_tripleDifference_two
import Theorems.Thm_Sabidussi_tripleDifference_zero
attribute [local simp] Sabidussi.bracketRightHom_apply
attribute [local simp] Sabidussi.bracket_self
attribute [local simp] Sabidussi.tripleDifference_one
attribute [local simp] Sabidussi.tripleDifference_two
attribute [local simp] Sabidussi.tripleDifference_zero



set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution {I : Type*} [Fintype I] [DecidableEq I]
    (f : I → Color) (c : Color) :
    ((colorFiber f c).card : F₂) = ∑ i, if f i = c then 1 else 0 := by
  symm
  simpa [colorFiber] using
    (Finset.sum_boole (R := F₂) (fun i ↦ f i = c) Finset.univ)
end Sabidussi
