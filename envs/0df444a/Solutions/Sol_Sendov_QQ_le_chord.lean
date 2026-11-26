-- Prove2me | solution 1 for Sendov.QQ_le_chord
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:02.739891+00:00
-- url     : https://prove2.me/submissions/7f653ddd-ece4-4f2d-ac95-1eecf2590b99

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic

set_option autoImplicit false
open Sendov
variable {c A t : ℝ}
namespace Sendov
theorem _root_.solution (ht0 : 0 ≤ t) (ht : A * t ≤ c) : QQ c A t ≤ 1 - c * t := by
  simp only [QQ]
  nlinarith [mul_nonneg ht0 (sub_nonneg.2 ht)]
end Sendov
