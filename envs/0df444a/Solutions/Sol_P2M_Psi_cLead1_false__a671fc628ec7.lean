-- Prove2me | solution 1 for P2M_Psi_cLead1_false__a671fc628ec7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:46:27.759354+00:00
-- url     : https://prove2.me/submissions/a2ec5315-f0ce-47b4-abe5-95dafd919953

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (r : List Bool) : cLead1 (false :: r) = 0 := rfl
end Psi
