-- Prove2me | solution 1 for Sendov.wsumZ_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:02:33.891909+00:00
-- url     : https://prove2.me/submissions/083eb5f8-d07d-4408-9a31-2edf40c8c929

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (L : ℤ) (i : ℕ) : wsumZ L i [] = 0 := rfl
end Sendov
