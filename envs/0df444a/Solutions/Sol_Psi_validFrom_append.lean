-- Prove2me | solution 1 for Psi.validFrom_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:50:57.249985+00:00
-- url     : https://prove2.me/submissions/179d3d5a-2ba6-44bf-8708-12d760457466

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p q : List Bool) (h : Int) :
    validFrom (p ++ q) h ↔ validFrom p h ∧ validFrom q (runHeight p h) := by
  induction p generalizing h with
  | nil => simp [validFrom, runHeight]
  | cons a t ih => cases a <;> simp [validFrom, runHeight, ih, and_assoc]
end Psi
