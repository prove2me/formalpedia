-- Prove2me | solution 1 for P2M_Psi_cLead1_true__c593a1b3f5d3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T23:46:11.80702+00:00
-- url     : https://prove2.me/submissions/6ed9161e-4709-41d6-a68c-1e82e7fce907

import Definitions.Def_RequestProject_Psi_Forward
import Definitions.Def_RequestProject_Psi_Inverse

set_option autoImplicit true
open Psi
namespace Psi
theorem _root_.solution (r : List Bool) : cLead1 (true :: r) = 1 + cLead1 r := rfl
end Psi
