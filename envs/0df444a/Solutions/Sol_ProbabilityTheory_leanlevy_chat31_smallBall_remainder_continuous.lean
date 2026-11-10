-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat31_smallBall_remainder_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:51:32.579538+00:00
-- url     : https://prove2.me/submissions/ddf72b53-b1f9-4084-905b-b893523ba2ad

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Topology.Defs.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

/-- Continuity of the source third-order exponential remainder. -/
theorem solution (ξ : ℝ) :
    Continuous (fun x : ℝ =>
      exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I
        + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) := by
  have h1 : Continuous (fun x : ℝ => (↑x : ℂ) * ↑ξ * I) :=
    (Complex.continuous_ofReal.mul continuous_const).mul continuous_const
  have h2 : Continuous (fun x : ℝ => ((↑x : ℂ) * ↑ξ) ^ 2 / 2) :=
    (((Complex.continuous_ofReal.mul continuous_const).pow 2)).div_const 2
  exact (((Complex.continuous_exp.comp h1).sub continuous_const).sub h1).add h2
