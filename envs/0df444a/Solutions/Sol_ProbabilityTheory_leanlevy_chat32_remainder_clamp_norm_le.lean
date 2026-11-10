-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat32_remainder_clamp_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:47:17.96695+00:00
-- url     : https://prove2.me/submissions/d49def35-cf52-4de0-a14e-4d5616c19509

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_continuous
import Theorems.Thm_ProbabilityTheory_leanlevy_chat31_smallBall_remainder_norm_le_crude
import Mathlib.Tactic.Linarith
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (ξ x : ℝ) :
    ‖(fun y : ℝ => exp ((↑y : ℂ) * ↑ξ * I) - 1 - (↑y : ℂ) * ↑ξ * I + ((↑y : ℂ) * ↑ξ) ^ 2 / 2)
        (max (-r) (min x r))‖ ≤ 2 + |ξ| + ξ ^ 2 / 2 := by
  have hc : |max (-r) (min x r)| ≤ 1 := by
    have h1 : max (-r) (min x r) ≤ r := max_le (by linarith) (min_le_right _ _)
    have h2 : -r ≤ max (-r) (min x r) := le_max_left _ _
    rw [abs_le]; exact ⟨by linarith, by linarith⟩
  exact ProbabilityTheory.leanlevy_chat31_smallBall_remainder_norm_le_crude hc
