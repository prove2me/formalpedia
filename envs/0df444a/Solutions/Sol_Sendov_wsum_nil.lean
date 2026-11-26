-- Prove2me | solution 1 for Sendov.wsum_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:01:56.292015+00:00
-- url     : https://prove2.me/submissions/2f12cf08-86d3-4333-8571-e6e8d89cf232

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (L : ℤ) (i : ℕ) : wsum L i [] = [] := rfl
end Sendov
