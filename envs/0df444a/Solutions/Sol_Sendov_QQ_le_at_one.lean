-- Prove2me | solution 1 for Sendov.QQ_le_at_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:05.671669+00:00
-- url     : https://prove2.me/submissions/518c6864-1374-4aef-b897-65802cda2b92

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_Common_Quadratic

set_option autoImplicit false
open Sendov
variable {c A t : ℝ}
namespace Sendov
theorem _root_.solution (hA : 0 ≤ A) (ht : c ≤ A * t) (ht1 : t ≤ 1) : QQ c A t ≤ QQ c A 1 := by
  have hkey : 0 ≤ A * (1 + t) - 2 * c := by nlinarith [ht, hA, ht1]
  simp only [QQ]
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) hkey]
end Sendov
