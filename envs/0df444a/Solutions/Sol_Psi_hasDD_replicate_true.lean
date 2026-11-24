-- Prove2me | solution 1 for Psi.hasDD_replicate_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:57:57.840022+00:00
-- url     : https://prove2.me/submissions/0f05b676-28ca-4f2a-874c-f124e249bd7b

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_hasDD_cons

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (n : Nat) : hasDD (List.replicate n true) = false := by
  induction n with
  | zero => rfl
  | succ m ih => rw [List.replicate_succ, hasDD_cons]; simp [ih]
end Psi
