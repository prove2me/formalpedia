-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_3_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:16.503843+00:00
-- url     : https://prove2.me/submissions/e1fe9d7f-0df0-4bd1-b278-211a1a4bd0d4

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution :
    Lcomb = graph (fun x => funOf (funOf x (ofNat 1)) (funOf x (ofNat 2))) :=
  rfl
end Scott1976.DataTypesAsLattices
