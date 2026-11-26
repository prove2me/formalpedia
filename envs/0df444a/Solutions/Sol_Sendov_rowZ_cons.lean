-- Prove2me | solution 1 for Sendov.rowZ_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:01:48.863523+00:00
-- url     : https://prove2.me/submissions/f54746ee-1674-462b-85a5-6c26fe1961be

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (p : List ℤ) (r : List (List ℤ)) (β : ℤ) :
    rowZ (p :: r) β = pevZ p β :: rowZ r β := rfl
end Sendov
