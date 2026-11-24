-- Prove2me | solution 1 for Psi.firstDDidx_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:58:23.200699+00:00
-- url     : https://prove2.me/submissions/419fb19d-1026-4e82-abc5-be8f7f1bfac7

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (r : List Bool) :
    firstDDidx (true :: r) = (firstDDidx r).map (· + 1) := rfl
end Psi
