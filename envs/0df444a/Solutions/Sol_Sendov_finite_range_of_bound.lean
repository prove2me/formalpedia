-- Prove2me | solution 1 for Sendov.finite_range_of_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:08:21.392808+00:00
-- url     : https://prove2.me/submissions/3ebe2004-9b5a-4fe7-ac62-7d0c6a51526d

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Reduce
import Theorems.Thm_Sendov_R_le_of_integral_le


set_option autoImplicit false
open Sendov
open MeasureTheory Finset
variable {n : ℕ} {α w : ℝ}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) (hα : 0 ≤ α) {J : ℝ}
    (hJ : (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)) ≤ J)
    (h : 1 / 6 + 1 / (4 * (3 + α)) + 1 / (2 * M n) + 1 / (4 * M n * (3 + α))
      + A n α ^ 2 * n * M n * ((n : ℝ) - 2) / (4 * (3 + α)) * J < 1) :
    R n α < 1 :=
  lt_of_le_of_lt (R_le_of_integral_le hn hα hJ) h
end Sendov
