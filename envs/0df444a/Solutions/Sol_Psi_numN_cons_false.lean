-- Prove2me | solution 1 for Psi.numN_cons_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:53:09.898691+00:00
-- url     : https://prove2.me/submissions/1168d7fe-2c0b-4ff9-8219-badd59ae4e26

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (t : List Bool) : numN (false :: t) = numN t := by
  simp [numN]
end Psi
