-- Prove2me | solution 1 for Sendov.Worigin_im
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:04:59.276109+00:00
-- url     : https://prove2.me/submissions/50f7c12e-af41-4a42-8da3-456b0f09405c

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
import Theorems.Thm_Sendov_Worigin_eq

set_option autoImplicit false
open Sendov
open Complex (I)
namespace Sendov
theorem _root_.solution (n : ℕ) (a x y : ℝ) : (Worigin n a x y).im = -(a * y) := by
  rw [Worigin_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring
end Sendov
