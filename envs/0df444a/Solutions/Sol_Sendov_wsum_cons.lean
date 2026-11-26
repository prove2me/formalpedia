-- Prove2me | solution 1 for Sendov.wsum_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:01:57.080802+00:00
-- url     : https://prove2.me/submissions/e6c51e1f-af3a-4c50-b0fb-7e77bd7e3e83

import Definitions.Def_Sendov_FiniteRange_Pack
import Definitions.Def_Sendov_FiniteRange_Recurrence
import Definitions.Def_Sendov_FiniteRange_PackBridge

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution (L : ℤ) (i : ℕ) (p : List ℤ) (r : List (List ℤ)) :
    wsum L i (p :: r)
      = padd (p.map (fun c => (L / ((i : ℤ) + 4)) * c)) (wsum L (i + 1) r) := rfl
end Sendov
