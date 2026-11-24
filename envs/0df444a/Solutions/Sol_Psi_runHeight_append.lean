-- Prove2me | solution 1 for Psi.runHeight_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:50:56.15192+00:00
-- url     : https://prove2.me/submissions/baedc457-e420-4b35-b117-1d9f243cc4e8

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p q : List Bool) (h : Int) :
    runHeight (p ++ q) h = runHeight q (runHeight p h) := by
  induction p generalizing h with
  | nil => simp [runHeight]
  | cons a t ih => cases a <;> simp [runHeight, ih]
end Psi
