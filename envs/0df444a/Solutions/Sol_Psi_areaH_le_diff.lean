-- Prove2me | solution 1 for Psi.areaH_le_diff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:31:36.324824+00:00
-- url     : https://prove2.me/submissions/19a95fd2-11c5-42aa-9fc0-3279a326af06

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (q : List Bool) (ht : Int) :
    areaH q ht true - areaH q ht false = (if q.head? = some true then ht else 0) := by
  cases q with
  | nil => simp [areaH]
  | cons a r => cases a <;> simp [areaH]
end Psi
