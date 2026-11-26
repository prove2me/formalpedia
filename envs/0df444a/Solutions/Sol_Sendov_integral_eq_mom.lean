-- Prove2me | solution 1 for Sendov.integral_eq_mom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:05:14.360471+00:00
-- url     : https://prove2.me/submissions/6e25ac15-5f61-4c0e-9c96-d41211a8883a

import Definitions.Def_Sendov_FiniteRange_Moments
import Definitions.Def_Sendov_FiniteRange_OddBound
import Definitions.Def_Sendov_FiniteRange_Reduce
import Theorems.Thm_Sendov_integral_moment


set_option autoImplicit false
open Sendov
open MeasureTheory Finset
variable {n : ℕ} {α w : ℝ}
namespace Sendov
theorem _root_.solution (k : ℕ) (hk : ((n : ℝ) - 4) / 2 = (k : ℕ)) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ (((n : ℝ) - 4) / 2)) = mom n α k := by
  rw [hk]
  simp only [Real.rpow_natCast]
  exact integral_moment n α k
end Sendov
