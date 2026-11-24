-- Prove2me | solution 1 for Psi.areaH_shift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:30:15.15695+00:00
-- url     : https://prove2.me/submissions/63514ec7-1202-4acf-ba8a-3312de5653bc

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (ht d : Int) (le : Bool) :
    areaH p (ht + d) le = areaH p ht le + d * (countValleys p le) := by
  induction p generalizing ht le with
  | nil => simp [areaH, countValleys]
  | cons a t ih =>
    cases a with
    | true =>
      simp only [areaH, countValleys]
      rw [show ht + d + 1 = (ht + 1) + d from by ring, ih]
      cases le <;> (simp <;> ring)
    | false =>
      simp only [areaH, countValleys]
      rw [show ht + d - 1 = (ht - 1) + d from by ring, ih]
end Psi
