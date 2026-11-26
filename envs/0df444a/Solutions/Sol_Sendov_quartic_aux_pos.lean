-- Prove2me | solution 1 for Sendov.quartic_aux_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:05:38.964041+00:00
-- url     : https://prove2.me/submissions/65aa45ce-5a39-4e5e-bfa3-dc0d908d1706

import Definitions.Def_Sendov_Analytic_Polar
import Definitions.Def_Sendov_Analytic_LowDegree

set_option autoImplicit false
open Sendov
namespace Sendov
theorem _root_.solution {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < a ^ 4 - 3 * a ^ 3 + 3 * a + 4 := by
  have hfactor : a ^ 4 - 3 * a ^ 3 + 3 * a + 4
      = 2 + 3 * a + (1 - a) * (2 + 2 * a + a ^ 2 * (2 - a)) := by ring
  have h1 : (0 : ℝ) < 1 - a := by linarith
  have h2 : (0 : ℝ) < 2 - a := by linarith
  rw [hfactor]
  positivity
end Sendov
