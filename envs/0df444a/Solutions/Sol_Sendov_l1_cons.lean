-- Prove2me | solution 1 for Sendov.l1_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:01:52.298515+00:00
-- url     : https://prove2.me/submissions/57a0288e-dc75-436a-bbc8-a511816f3fa9

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (a : ℤ) (p : List ℤ) : l1 (a :: p) = |a| + l1 p := rfl
end Sendov
