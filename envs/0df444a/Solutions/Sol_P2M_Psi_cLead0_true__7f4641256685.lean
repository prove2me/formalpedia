-- Prove2me | solution 1 for P2M_Psi_cLead0_true__7f4641256685
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:46:02.83808+00:00
-- url     : https://prove2.me/submissions/0b144ad8-23c7-4713-a5c2-41144347db43

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (r : List Bool) : cLead0 (true :: r) = 0 := rfl
end Psi
