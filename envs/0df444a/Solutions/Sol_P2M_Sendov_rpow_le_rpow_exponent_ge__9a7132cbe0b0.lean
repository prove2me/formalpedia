-- Prove2me | solution 1 for P2M_Sendov_rpow_le_rpow_exponent_ge__9a7132cbe0b0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:00:05.147028+00:00
-- url     : https://prove2.me/submissions/d8ae48f8-9592-4426-985a-fe102aec21ba

import Definitions.Def_Sendov_Common_Rpow
import Definitions.Def_Sendov_FiniteRange_Batch

set_option autoImplicit false
open Sendov
variable {α t : ℝ}
open MeasureTheory
namespace Sendov
theorem _root_.solution {x y z : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hz : 0 < z)
    (hzy : z ≤ y) : x ^ y ≤ x ^ z := by
  rcases eq_or_lt_of_le hx0 with h | h
  · rw [← h, Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
  · exact Real.rpow_le_rpow_of_exponent_ge h hx1 hzy
end Sendov
