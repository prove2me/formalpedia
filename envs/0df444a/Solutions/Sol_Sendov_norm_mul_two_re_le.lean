-- Prove2me | solution 1 for Sendov.norm_mul_two_re_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:04:56.560835+00:00
-- url     : https://prove2.me/submissions/5e12c3d7-b00c-4976-aeab-09b252f28593

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact

set_option autoImplicit false
open Sendov
open Complex (I)
namespace Sendov
theorem _root_.solution {w : ℂ} (_hs : 0 < w.re) :
    ‖w‖ * (2 * w.re) ≤ 2 * w.re ^ 2 + w.im ^ 2 := by
  have h1 : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  nlinarith [norm_nonneg w, h1, sq_nonneg (w.im ^ 2), sq_nonneg (w.re * w.im)]
end Sendov
