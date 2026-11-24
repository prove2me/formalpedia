-- Prove2me | solution 1 for Psi.stEast_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:57:23.666861+00:00
-- url     : https://prove2.me/submissions/8833684a-4532-42cc-abba-3c6dd2678dfc

import Definitions.Def_RequestProject_Psi_Defs
import Definitions.Def_RequestProject_Psi_PathLemmas

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (p : List Bool) (hp : p ≠ []) (x y : Bool) :
    stEast p x = stEast p y := by
  induction p generalizing x y with
  | nil => exact absurd rfl hp
  | cons a t ih => cases t with
      | nil => cases a <;> simp [stEast]
      | cons b s => cases a <;> exact ih (by simp) _ _
end Psi
