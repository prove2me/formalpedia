-- Prove2me | solution 1 for Sendov.A_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:54:21.044013+00:00
-- url     : https://prove2.me/submissions/96d512c1-63eb-4ff6-8aae-0a7ba542f6a1

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (hfeas : c n α ^ 2 ≤ A n α) : 0 ≤ A n α :=
  le_trans (sq_nonneg _) hfeas
end Sendov
