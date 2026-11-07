-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat15_one_sub_sinc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:36:32.852876+00:00
-- url     : https://prove2.me/submissions/e0777636-31b8-460a-b556-60df27bbba9b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- The sinc damping factor is nonnegative on the real line. -/
theorem solution (x : ℝ) : 0 ≤ 1 - Real.sinc x := by
  have hs : Real.sinc x ≤ 1 := Real.sinc_le_one x
  linarith
