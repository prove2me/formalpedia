-- Prove2me | solution 1 for PIW.FdPA.rh_facts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:22:00.580799+00:00
-- url     : https://prove2.me/submissions/36594c63-9514-499a-a3ab-9efcf3555663

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_ZnNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainExtension_PointAssembly_DivLeExpOfAbsLogSubLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PIW PIW.FdPA
open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex Metric
noncomputable section
namespace PIW.FdPA
theorem _root_.solution {c1 w : ℝ} (hc1 : 0 < c1) (hw1 : 1 ≤ w) :
    0 < d6rh c1 w ∧ d6rh c1 w < 1 / 10 ∧ w * d6rh c1 w ≤ 1 / 36 := by
  unfold ReciprocityTheory.ChartRestriction.G.FD.d6rh
  have hpi := Real.pi_gt_three
  have hw0 : 0 < w := by linarith
  have hpos : 0 < 12 * Real.pi * (c1 + w) := by positivity
  have hp3 : (0 : ℝ) < Real.pi - 3 := by linarith
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_lt_div_iff₀ hpos (by norm_num)]
    nlinarith [mul_pos hc1 hp3, mul_pos hw0 hp3]
  · rw [mul_one_div, div_le_div_iff₀ hpos (by norm_num)]
    nlinarith [mul_pos hc1 hp3, mul_pos hw0 hp3]
end PIW.FdPA
