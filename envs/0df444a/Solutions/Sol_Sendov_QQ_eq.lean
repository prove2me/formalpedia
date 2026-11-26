-- Prove2me | solution 1 for Sendov.QQ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:56:25.962662+00:00
-- url     : https://prove2.me/submissions/363c7b6a-5fb0-4a1b-8cda-f3e3f6d39bdb

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic

set_option autoImplicit false
open Sendov
variable {c A t : ℝ}
namespace Sendov
theorem _root_.solution (c A t : ℝ) : QQ c A t = (1 - c * t) ^ 2 + (A - c ^ 2) * t ^ 2 := by
  simp only [QQ]; ring
end Sendov
