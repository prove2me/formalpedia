-- Prove2me | solution 1 for Sabidussi.localDifference_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:12:25.226881+00:00
-- url     : https://prove2.me/submissions/a85ce48f-181f-4045-b07f-6911f7ae9cc1

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_LocalPattern
import Theorems.Thm_Sabidussi_choiceColor_ne_zero
import Theorems.Thm_Sabidussi_doubleDifference_ne_zero
import Theorems.Thm_Sabidussi_tripleDifference_ne_zero


set_option autoImplicit true
open Sabidussi
open scoped BigOperators
namespace Sabidussi
theorem _root_.solution (n : ℕ) (c : Fin 3) (i : Fin (n + 2)) :
    localDifference n c i ≠ 0 := by
  induction n using Nat.twoStepInduction with
  | zero => exact doubleDifference_ne_zero _ (choiceColor_ne_zero c) i
  | one => exact tripleDifference_ne_zero _ (choiceColor_ne_zero c) i
  | more n ih _ =>
      refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ih k) j) i
      · exact choiceColor_ne_zero c
      · exact choiceColor_ne_zero c
end Sabidussi
