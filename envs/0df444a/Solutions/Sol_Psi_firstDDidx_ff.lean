-- Prove2me | solution 1 for Psi.firstDDidx_ff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:02:52.222833+00:00
-- url     : https://prove2.me/submissions/c82d56ce-e3a5-4e01-9b19-b4c2088c8d93

import Definitions.Def_RequestProject_Psi_RiseComp
import Definitions.Def_RequestProject_Psi_Forward

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (r : List Bool) : firstDDidx (false :: false :: r) = some 0 := rfl
end Psi
