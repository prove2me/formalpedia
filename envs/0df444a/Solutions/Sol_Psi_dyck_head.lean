-- Prove2me | solution 1 for Psi.dyck_head
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:54:52.664627+00:00
-- url     : https://prove2.me/submissions/0c3a7d64-cc98-43f9-a5aa-c14d5e9b6975

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (hd : IsDyck p) (hne : p ≠ []) : p.head? = some true := by
  cases p with
  | nil => exact absurd rfl hne
  | cons a t => cases a with
      | true => rfl
      | false => simp only [IsDyck, IsDyckAux] at hd; omega
end Psi
