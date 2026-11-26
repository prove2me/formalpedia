-- Prove2me | solution 1 for Sendov.integral_exp_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:44:08.223063+00:00
-- url     : https://prove2.me/submissions/018c3642-3296-4ca9-a55a-aec2ff55d7cf

import Definitions.Def_Sendov_Reduction_Polar
import Definitions.Def_Sendov_Common_Sinh
import Definitions.Def_Sendov_Reduction_BetaBound

set_option autoImplicit false
open Sendov
open MeasureTheory Real
variable {α B c : ℝ}
namespace Sendov
theorem _root_.solution (hc : c ≠ 0) (a b : ℝ) :
    (∫ t in a..b, exp (c * t)) = (exp (c * b) - exp (c * a)) / c := by
  have h := intervalIntegral.integral_comp_mul_left (a := a) (b := b) (fun y : ℝ => exp y) hc
  rw [h, integral_exp]
  simp only [smul_eq_mul]
  field_simp
end Sendov
