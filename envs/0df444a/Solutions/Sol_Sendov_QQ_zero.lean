-- Prove2me | solution 1 for Sendov.QQ_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:07:42.342324+00:00
-- url     : https://prove2.me/submissions/144c93ad-799c-47dd-a176-c16ea0951623

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic

set_option autoImplicit false
open Sendov
variable {c A t : ℝ}
namespace Sendov
theorem _root_.solution (c A : ℝ) : QQ c A 0 = 1 := by simp [QQ]
end Sendov
