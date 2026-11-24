-- Prove2me | solution 1 for Psi.isDyckAux_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:50:55.17884+00:00
-- url     : https://prove2.me/submissions/0ce555f2-2c49-4074-87b9-14d195ac7983

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (h : Int) :
    IsDyckAux p h ↔ validFrom p h ∧ runHeight p h = 0 := by
  induction p generalizing h with
  | nil => simp [IsDyckAux, validFrom, runHeight]
  | cons a t ih => cases a <;> simp [IsDyckAux, validFrom, runHeight, ih, and_assoc]
end Psi
