-- Prove2me | solution 1 for Sendov.three_add_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:53:49.870862+00:00
-- url     : https://prove2.me/submissions/16a7bc72-b0b9-4f10-85b4-ba1c3cc88143

import Definitions.Def_Sendov_Defs
import Definitions.Def_Sendov_Common_Basic

set_option autoImplicit false
open Sendov
variable {n : ℕ} {α t : ℝ}
namespace Sendov
theorem _root_.solution (hα : 0 ≤ α) : (0 : ℝ) < 3 + α := by linarith
end Sendov
