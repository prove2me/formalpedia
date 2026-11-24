-- Prove2me | solution 1 for Psi.firstDDidx_ft
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:02:56.617068+00:00
-- url     : https://prove2.me/submissions/947c920c-220e-451d-a5c1-52d675efdf39

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (r : List Bool) :
    firstDDidx (false :: true :: r) = (firstDDidx (true :: r)).map (· + 1) := rfl
end Psi
