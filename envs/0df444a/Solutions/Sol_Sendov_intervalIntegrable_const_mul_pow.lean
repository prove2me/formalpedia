-- Prove2me | solution 1 for Sendov.intervalIntegrable_const_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:54:06.518955+00:00
-- url     : https://prove2.me/submissions/cf9a75cc-b06c-4649-80af-ab190f7c1dc4

import Definitions.Def_Sendov_Common_Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Definitions.Def_Sendov_FiniteRange_Moments

set_option autoImplicit false
open Sendov
open MeasureTheory Finset
namespace Sendov
theorem _root_.solution (a : ℝ) (m : ℕ) :
    IntervalIntegrable (fun t : ℝ => a * t ^ m) volume 0 1 :=
  (by fun_prop : Continuous fun t : ℝ => a * t ^ m).intervalIntegrable _ _
end Sendov
