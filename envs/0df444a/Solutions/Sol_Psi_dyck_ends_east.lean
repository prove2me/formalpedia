-- Prove2me | solution 1 for Psi.dyck_ends_east
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:26:56.091837+00:00
-- url     : https://prove2.me/submissions/b8fd0d00-9aa0-4698-899f-eb13b89464dd

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas
import Theorems.Thm_Psi_runHeight_append
import Theorems.Thm_Psi_validFrom_append
import Theorems.Thm_Psi_isDyckAux_iff
import Theorems.Thm_Psi_runHeight_nonneg

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (hd : IsDyck p) (hne : p ≠ []) :
    p.getLast? = some false := by
  obtain ⟨ys, y, rfl⟩ := (List.eq_nil_or_concat p).resolve_left hne
  rw [List.concat_eq_append] at hd ⊢
  cases y with
  | false => simp
  | true =>
      exfalso
      rw [IsDyck, isDyckAux_iff, validFrom_append] at hd
      have h1 : runHeight (ys ++ [true]) 0 = runHeight ys 0 + 1 := by
        rw [runHeight_append]; simp [runHeight]
      have := runHeight_nonneg ys 0 le_rfl hd.1.1
      rw [h1] at hd; omega
end Psi
