-- Prove2me | solution 1 for Sabidussi.triple_local_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:15:44.507608+00:00
-- url     : https://prove2.me/submissions/f7c3c0da-3170-44b5-b6d0-9356be0562f0

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_tripleDifference_zero
import Theorems.Thm_Sabidussi_tripleDifference_one
import Theorems.Thm_Sabidussi_tripleDifference_two
attribute [local simp] Sabidussi.bracketRightHom_apply
attribute [local simp] Sabidussi.bracket_self
attribute [local simp] Sabidussi.tripleDifference_zero
attribute [local simp] Sabidussi.tripleDifference_one
attribute [local simp] Sabidussi.tripleDifference_two

set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (t : Color) :
    (∑ i, quadratic (tripleDifference t i)) +
      (∑ i, ∑ j,
        if j < i then bracket (tripleDifference t i) (tripleDifference t j) else 0) = 0 := by
  simp only [Fin.sum_univ_three, tripleDifference, quadratic, bracket]
  split_ifs <;> try omega
  ring_nf
  rw [show (8 : F₂) = 0 from (show Even 8 by exact ⟨4, rfl⟩).natCast_zmod_two,
    show (4 : F₂) = 0 from (show Even 4 by exact ⟨2, rfl⟩).natCast_zmod_two]
  simp
end Sabidussi
