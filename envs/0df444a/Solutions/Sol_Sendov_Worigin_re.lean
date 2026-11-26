-- Prove2me | solution 1 for Sendov.Worigin_re
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:58:06.853856+00:00
-- url     : https://prove2.me/submissions/f79cd918-5267-4d5c-bb42-390a2fbcd7f3

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
import Theorems.Thm_Sendov_Worigin_eq

set_option autoImplicit false
open Sendov
open Complex (I)
namespace Sendov
theorem _root_.solution (n : ℕ) (a x y : ℝ) :
    (Worigin n a x y).re = a ^ 2 * ((n : ℝ) - 1) + 1 - a * x := by
  rw [Worigin_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring
end Sendov
