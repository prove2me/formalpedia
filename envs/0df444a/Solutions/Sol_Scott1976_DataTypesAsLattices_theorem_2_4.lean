-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_2_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:13.650565+00:00
-- url     : https://prove2.me/submissions/b6d1643c-2cad-48f2-b858-205925c78b5a

import Definitions.Def_Scott1976_DataTypesAsLattices_Embedding
import Definitions.Def_Scott1976_DataTypesAsLattices_Lambda

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution : IsCombinatory zeroC ∧ IsCombinatory sucC ∧ IsCombinatory predC ∧
    IsCombinatory condC ∧ IsCombinatory Kcomb ∧ IsCombinatory Scomb :=
  ⟨.zero, .suc, .pred, .cond, .K, .S⟩
end Scott1976.DataTypesAsLattices
