-- Prove2me | solution 1 for Sendov.Ppolar_le_lin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:59:39.240092+00:00
-- url     : https://prove2.me/submissions/94daedfc-7d69-4576-b818-a06adedb071b

import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Reduction_Polar

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution (a x : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Ppolar a x t ≤ 1 + (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t) := by
  have hid : 1 + (1 - a ^ 2) * (-1 + (2 - QQ (a * x) (a ^ 2) 1) * t) - Ppolar a x t
      = (1 - a ^ 2) ^ 2 * (t - t ^ 2) := by
    simp only [Ppolar, QQ]; ring
  nlinarith [mul_nonneg (sq_nonneg (1 - a ^ 2)) (mul_nonneg ht0 (sub_nonneg.2 ht1))]
end Sendov
