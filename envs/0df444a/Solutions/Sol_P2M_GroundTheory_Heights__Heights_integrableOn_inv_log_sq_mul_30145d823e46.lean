-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_integrableOn_inv_log_sq_mul_30145d823e46
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:32.54689+00:00
-- url     : https://prove2.me/submissions/d5d253c2-f070-4984-b61a-a7e9d08e8c46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepWeightMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepWeightMass

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    IntegrableOn (fun r : ℝ => ((Real.log r) ^ 2 * r)⁻¹) (Set.Ioc 0 (Real.exp (-(Real.exp 1 / 2)))) := by
  have hρ1 : Real.exp (-(Real.exp 1 / 2)) < 1 :=
    Real.exp_lt_one_iff.2 (by have := Real.exp_pos 1; linarith)
  have hcont0 : ContinuousAt (fun r : ℝ => -(Real.log r)⁻¹) 0 := by
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    simpa using (Real.tendsto_log_nhdsNE_zero.inv_tendsto_atBot).neg
  refine intervalIntegral.integrableOn_deriv_of_nonneg (g := fun r : ℝ => -(Real.log r)⁻¹) ?_ ?_ ?_
  · intro x hx
    rcases eq_or_lt_of_le hx.1 with h | h
    · subst h
      exact hcont0.continuousWithinAt
    · have hl : Real.log x ≠ 0 := (Real.log_neg h (hx.2.trans_lt hρ1)).ne
      exact ((Real.continuousAt_log h.ne').inv₀ hl).neg.continuousWithinAt
  · intro x hx
    have hl : Real.log x ≠ 0 := (Real.log_neg hx.1 (hx.2.trans hρ1)).ne
    have hx0 : x ≠ 0 := hx.1.ne'
    have : HasDerivAt (fun r : ℝ => -(Real.log r)⁻¹) (-(-x⁻¹ / Real.log x ^ 2)) x :=
      ((Real.hasDerivAt_log hx0).inv hl).neg
    refine this.congr_deriv ?_
    rw [neg_div, neg_neg]
    ring
  · intro x hx
    exact inv_nonneg.2 (mul_nonneg (sq_nonneg _) hx.1.le)
end GroundTheory.Heights₂.Heights
