-- Prove2me | solution 1 for Psi.countValleys_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:56:56.902996+00:00
-- url     : https://prove2.me/submissions/f874e6b6-6b8e-40f0-93aa-b5347757eee1

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p q : List Bool) (le : Bool) :
    countValleys (p ++ q) le = countValleys p le + countValleys q (stEast p le) := by
  induction p generalizing le with
  | nil => simp [countValleys, stEast]
  | cons a t ih => cases a <;> (simp [countValleys, stEast, ih] <;> omega)
end Psi
