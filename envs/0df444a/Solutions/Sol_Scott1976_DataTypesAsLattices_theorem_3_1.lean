-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:50.078837+00:00
-- url     : https://prove2.me/submissions/6274490c-eb75-4a9b-9f38-1089dfb1f710

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution {u : Pomega} (hu : IsCombinatory u) :
    IsCombinatory u := hu
end Scott1976.DataTypesAsLattices
