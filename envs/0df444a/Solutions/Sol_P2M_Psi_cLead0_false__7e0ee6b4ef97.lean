-- Prove2me | solution 1 for P2M_Psi_cLead0_false__7e0ee6b4ef97
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:46:02.00294+00:00
-- url     : https://prove2.me/submissions/9bcae827-ddde-415a-94f0-eeae6d1a39b6

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (r : List Bool) : cLead0 (false :: r) = 1 + cLead0 r := rfl
end Psi
