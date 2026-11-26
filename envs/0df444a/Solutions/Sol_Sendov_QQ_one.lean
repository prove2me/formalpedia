-- Prove2me | solution 1 for Sendov.QQ_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:56:31.865034+00:00
-- url     : https://prove2.me/submissions/a5f29dbe-47a6-4d12-8651-d05eea8ec25d

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic

set_option autoImplicit false
open Sendov
variable {c A t : ℝ}
namespace Sendov
theorem _root_.solution (c A : ℝ) : QQ c A 1 = 1 - 2 * c + A := by simp [QQ]
end Sendov
