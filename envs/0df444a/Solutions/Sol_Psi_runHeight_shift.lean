-- Prove2me | solution 1 for Psi.runHeight_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:00:49.179571+00:00
-- url     : https://prove2.me/submissions/0588062a-483c-40bb-bd2e-a330df9deb54

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (h d : Int) :
    runHeight p (h + d) = runHeight p h + d := by
  induction p generalizing h with
  | nil => simp [runHeight]
  | cons a t ih => cases a with
    | true => simp only [runHeight]; rw [show h + d + 1 = (h + 1) + d from by ring, ih]
    | false => simp only [runHeight]; rw [show h + d - 1 = (h - 1) + d from by ring, ih]
end Psi
