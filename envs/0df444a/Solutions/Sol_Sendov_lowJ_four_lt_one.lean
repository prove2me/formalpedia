-- Prove2me | solution 1 for Sendov.lowJ_four_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:07:57.082113+00:00
-- url     : https://prove2.me/submissions/7c619b2b-ff79-4c23-8faf-d2a847ac50aa

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree
import Theorems.Thm_Sendov_lowJ_four_identity
import Theorems.Thm_Sendov_quartic_aux_pos

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : lowJ 4 a < 1 := by
  have haux := quartic_aux_pos ha0 ha1
  have h1 : (0 : ℝ) < 1 - a := by linarith
  have h2 : (0 : ℝ) < 1 + a := by linarith
  rw [← sub_pos, lowJ_four_identity]
  positivity
end Sendov
