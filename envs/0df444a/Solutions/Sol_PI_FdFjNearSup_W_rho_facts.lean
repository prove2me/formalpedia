-- Prove2me | solution 1 for PI.FdFjNearSup.W.rho_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:38:59.796272+00:00
-- url     : https://prove2.me/submissions/c0484f7d-ad51-4789-b2cb-69de1b5ab6db

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicCoefficientSplitting
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_NearSupremumBounds_FdFjNearSupOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.FdFjNearSup PI.FdFjNearSup.W
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace PI.FdFjNearSup.W
theorem _root_.solution {c1 w : ℝ} (hc1 : 0 < c1) (hw : 1 ≤ w) :
    0 < d6rh c1 w ∧ d6rh c1 w ≤ 1 / 36 ∧ 12 * Real.pi * (c1 + w) * d6rh c1 w = 1 := by
  have hp := Real.pi_gt_three
  have hA : 0 < 12 * Real.pi * (c1 + w) := by positivity
  have h36 : 36 ≤ 12 * Real.pi * (c1 + w) := by
    nlinarith [mul_le_mul_of_nonneg_right hp.le (by linarith : (0 : ℝ) ≤ c1 + w)]
  unfold d6rh
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_le_div_iff₀ hA (by norm_num)]
    linarith
  · field_simp
end PI.FdFjNearSup.W
