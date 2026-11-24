-- Prove2me | solution 1 for Psi.numN_cons_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:52:50.064803+00:00
-- url     : https://prove2.me/submissions/7f53b32d-8c62-431c-811e-63cad74dcde6

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (t : List Bool) : numN (true :: t) = numN t + 1 := by
  simp [numN]
end Psi
