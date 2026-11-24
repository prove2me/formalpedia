-- Prove2me | solution 1 for Psi.numNBeforeDD_cons_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:17:05.859131+00:00
-- url     : https://prove2.me/submissions/b0233807-2a66-4f30-81d8-03ce3ab8473a

import Definitions.Def_RequestProject_Psi_Inverse
import Definitions.Def_RequestProject_Psi_Bijection

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (r : List Bool) :
    numNBeforeDD (true :: r) = numNBeforeDD r + 1 := rfl
end Psi
