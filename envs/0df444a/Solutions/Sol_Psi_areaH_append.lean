-- Prove2me | solution 1 for Psi.areaH_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:01:56.025384+00:00
-- url     : https://prove2.me/submissions/fdd93a43-0de3-4621-b174-1a5f75d0eab9

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p q : List Bool) (ht : Int) (le : Bool) :
    areaH (p ++ q) ht le = areaH p ht le + areaH q (runHeight p ht) (stEast p le) := by
  induction p generalizing ht le with
  | nil => simp [areaH, runHeight, stEast]
  | cons a t ih => cases a <;> (simp [areaH, runHeight, stEast, ih] <;> ring)
end Psi
