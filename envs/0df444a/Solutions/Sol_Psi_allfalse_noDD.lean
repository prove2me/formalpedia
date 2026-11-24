-- Prove2me | solution 1 for Psi.allfalse_noDD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:41:38.43482+00:00
-- url     : https://prove2.me/submissions/df5f8d98-5d16-4738-a9f1-99225b0c0bff

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward
import Theorems.Thm_Psi_hasDD_cons
import Theorems.Thm_Psi_numN_cons_false
import Theorems.Thm_Psi_numN_cons_true


set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (xs : List Bool) (h0 : numN xs = 0) (hd : hasDD xs = false) :
    xs = [] ∨ xs = [false] := by
  match xs with
  | [] => left; rfl
  | [a] =>
      right; cases a with
      | false => rfl
      | true => rw [numN_cons_true] at h0; omega
  | a :: b :: rest =>
      exfalso
      have ha : a = false := by
        cases a with | false => rfl | true => rw [numN_cons_true] at h0; omega
      have hb : b = false := by
        cases b with
        | false => rfl
        | true => subst ha; rw [numN_cons_false, numN_cons_true] at h0; omega
      subst ha; subst hb; rw [hasDD_cons] at hd; simp at hd
end Psi
