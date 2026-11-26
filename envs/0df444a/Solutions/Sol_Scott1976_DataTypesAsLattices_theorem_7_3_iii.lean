-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_7_3_iii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:27.421008+00:00
-- url     : https://prove2.me/submissions/a30437e9-3b34-4d84-adb0-788af0848be3

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution :
    Scomb = graph (fun u => graph (fun v =>
      graph (fun x => funOf (funOf u x) (funOf v x)))) :=
  rfl
end Scott1976.DataTypesAsLattices
