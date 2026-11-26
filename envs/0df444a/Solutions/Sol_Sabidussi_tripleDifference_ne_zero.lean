-- Prove2me | solution 1 for Sabidussi.tripleDifference_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:09:08.486578+00:00
-- url     : https://prove2.me/submissions/5351e6aa-1484-43ea-b9ac-044439031c46

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
theorem _root_.solution (t : Color) (ht : t ≠ 0) (i : Fin 3) :
    tripleDifference t i ≠ 0 := by
  fin_cases i
  · simpa using ht
  · intro h
    apply ht
    rcases Prod.mk_eq_zero.mp h with ⟨h₂, hsum⟩
    ext
    · simpa [h₂] using hsum
    · exact h₂
  · intro h
    apply ht
    rcases Prod.mk_eq_zero.mp h with ⟨hsum, h₁⟩
    ext
    · exact h₁
    · simpa [h₁] using hsum
end Sabidussi
