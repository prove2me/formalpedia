-- Prove2me | solution 1 for Scott1976.DataTypesAsLattices.theorem_3_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:04:51.497805+00:00
-- url     : https://prove2.me/submissions/c6ef3c87-501f-42f1-9c88-683929556428

import Definitions.Def_Scott1976_DataTypesAsLattices_Computability
import Definitions.Def_Scott1976_DataTypesAsLattices_Enumeration

set_option autoImplicit true
open Scott1976 Scott1976.DataTypesAsLattices
namespace Scott1976.DataTypesAsLattices
theorem _root_.solution (v : ℕ → ℕ) (n : ℕ) :
    recNat v n = applyNat (v n) (num (v n)) := rfl
end Scott1976.DataTypesAsLattices
