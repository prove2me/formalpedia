-- Prove2me | solution 1 for Sendov.l1row_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:02:16.354896+00:00
-- url     : https://prove2.me/submissions/9fc3008f-8a0b-4ae5-b6e7-af93f03dfac5

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (p : List ℤ) (r : List (List ℤ)) :
    l1row (p :: r) = l1 p + l1row r := rfl
end Sendov
