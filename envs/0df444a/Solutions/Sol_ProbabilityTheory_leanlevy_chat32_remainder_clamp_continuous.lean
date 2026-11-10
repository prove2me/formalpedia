-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat32_remainder_clamp_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:47:09.543223+00:00
-- url     : https://prove2.me/submissions/463bd0de-95cc-4bd7-accc-c2a8daa07ebb

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_continuous
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_norm_le_crude
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (r : ℝ) (ξ : ℝ) :
    Continuous (fun x : ℝ =>
      (fun y : ℝ => exp ((↑y : ℂ) * ↑ξ * I) - 1 - (↑y : ℂ) * ↑ξ * I + ((↑y : ℂ) * ↑ξ) ^ 2 / 2)
        (max (-r) (min x r))) := by
  exact (ProbabilityTheory.leanlevy_chat31_smallBall_remainder_continuous ξ).comp
    (continuous_const.max (continuous_id.min continuous_const))
