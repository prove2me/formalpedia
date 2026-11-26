-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_7_2_i
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:07:13.091538+00:00
-- url     : https://prove2.me/submissions/2f8132bb-5700-479f-a316-eac7d30cdadb

import Definitions.Def_Scott1976_DataTypesAsLattices_Retracts
import Definitions.Def_Scott1976_DataTypesAsLattices_Functionality

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (a x y : Pomega) :
    (Ea a).rel x y ↔ typed x a ∧ typed y a ∧ x = y :=
  Iff.rfl
end Scott1976.DataTypesAsLattices
