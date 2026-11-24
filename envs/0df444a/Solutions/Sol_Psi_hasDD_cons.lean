-- Prove2me | solution 1 for Psi.hasDD_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:52:20.879494+00:00
-- url     : https://prove2.me/submissions/62110946-cc18-4b91-b8c4-357d8520cd52

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (a : Bool) (rest : List Bool) :
    hasDD (a :: rest) = ((a == false && rest.head? == some false) || hasDD rest) := by
  cases a with
  | true => cases rest with | nil => rfl | cons b u => simp [hasDD]
  | false => cases rest with
      | nil => rfl
      | cons b u => cases b <;> simp [hasDD]
end Psi
