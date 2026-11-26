-- Prove2me | solution 1 for Sabidussi.quadratic_sum_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:14.105477+00:00
-- url     : https://prove2.me/submissions/715e3a66-2412-4791-a795-76f6a0da8c4d

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Parity
import Theorems.Thm_Sabidussi_orderedPairBracket_succ
import Theorems.Thm_Sabidussi_bracketRightHom_apply
import Theorems.Thm_Sabidussi_bracket_self
import Theorems.Thm_Sabidussi_quadratic_add
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
theorem _root_.solution : ∀ {n : ℕ} (f : Fin n → Color),
    quadratic (∑ i, f i) = (∑ i, quadratic (f i)) + orderedPairBracket f
  | 0, f => by simp [orderedPairBracket, quadratic]
  | n + 1, f => by
    rw [Fin.sum_univ_castSucc, quadratic_add,
      solution (fun i : Fin n ↦ f i.castSucc), orderedPairBracket_succ,
      Fin.sum_univ_castSucc]
    abel
end Sabidussi
