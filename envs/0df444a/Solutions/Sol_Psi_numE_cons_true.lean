-- Prove2me | solution 1 for Psi.numE_cons_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:10:04.106481+00:00
-- url     : https://prove2.me/submissions/4af6338f-3e2d-4558-a082-d77ba409d1f2

import Definitions.Def_RequestProject_Psi_PhiBasic
import Definitions.Def_RequestProject_Psi_Area

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (t : List Bool) : numE (true :: t) = numE t := by
  simp [numE]
end Psi
