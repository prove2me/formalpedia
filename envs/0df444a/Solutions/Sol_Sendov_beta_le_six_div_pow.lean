-- Prove2me | solution 1 for Sendov.beta_le_six_div_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:07:48.702803+00:00
-- url     : https://prove2.me/submissions/f44905b8-72a2-4ee3-b14c-c648681d274a

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {s : ℝ} (hs : 0 < s) :
    6 / ((s + 1) * (s + 2) * (s + 3) * (s + 4)) ≤ 6 / s ^ 4 := by
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [hs.le, sq_nonneg s, sq_nonneg (s + 1)]
end Sendov
