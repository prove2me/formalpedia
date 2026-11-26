-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_3_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:51.068725+00:00
-- url     : https://prove2.me/submissions/81bdf2fb-c7c4-46d7-b700-38d63908ce37

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution :
    zeroC ∈ RE ∧ sucC ∈ RE ∧ predC ∈ RE ∧ condC ∈ RE ∧
      Kcomb ∈ RE ∧ Scomb ∈ RE :=
  ⟨.zero, .suc, .pred, .cond, .K, .S⟩
end Scott1976.DataTypesAsLattices
