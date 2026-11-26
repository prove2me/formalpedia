-- Prove2me | solution 1 for Sendov.continuous_deriv_seg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:02:36.31844+00:00
-- url     : https://prove2.me/submissions/77e322fe-0c55-4e61-b472-0ad7c975147b

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
import Theorems.Thm_Sendov_sumEraseProd_zero
attribute [local simp] Sendov.sumEraseProd_zero

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
open MeasureTheory
namespace Sendov
theorem _root_.solution (p : ℂ[X]) (a w : ℂ) :
    Continuous fun t : ℝ => (derivative p).eval (a + (t : ℂ) * (w - a)) := by
  fun_prop
end Sendov
