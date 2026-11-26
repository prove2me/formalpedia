-- Prove2me | solution 1 for Sendov.collapse_J
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:05:04.584171+00:00
-- url     : https://prove2.me/submissions/ddfd9a03-7874-4872-82fe-3655f78ff1b6

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact

set_option autoImplicit false
open Sendov
open Complex (I)
namespace Sendov
theorem _root_.solution {K c P : ℝ} (hP1 : P ≤ 1) (hc0 : 0 ≤ c) (hcK : 2 * c ≤ K) :
    P * K + c * (1 - P ^ 2) ≤ K := by
  have hfac : 0 ≤ (1 - P) * (K - c * (1 + P)) := by
    refine mul_nonneg (by linarith) ?_
    nlinarith [hc0, hP1, hcK]
  nlinarith [hfac]
end Sendov
