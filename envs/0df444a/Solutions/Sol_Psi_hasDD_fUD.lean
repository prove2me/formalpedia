-- Prove2me | solution 1 for Psi.hasDD_fUD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:33:11.655809+00:00
-- url     : https://prove2.me/submissions/3b505d81-01f9-4031-b037-182b282b02e8

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area
import Theorems.Thm_Psi_hasDD_append_false
import Theorems.Thm_Psi_fUD_head

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : Nat) : hasDD (fUD a) = false := by
  induction a with
  | zero => rfl
  | succ m ih =>
    rw [fUD, List.replicate_succ, List.flatten_cons]
    exact hasDD_append_false _ _ rfl ih (fun _ => fUD_head m)
end Psi
