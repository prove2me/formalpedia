-- Prove2me | solution 1 for Sendov.wsumZ_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:02:41.731541+00:00
-- url     : https://prove2.me/submissions/12c08300-8619-48aa-9bb5-0bd34f3e01bf

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (L : ℤ) (i : ℕ) (a : ℤ) (s : List ℤ) :
    wsumZ L i (a :: s) = (L / ((i : ℤ) + 4)) * a + wsumZ L (i + 1) s := rfl
end Sendov
