-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.rm_I_smul_vec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:26:02.766284+00:00
-- url     : https://prove2.me/submissions/fd8da348-1a0f-403f-8ad1-5877c9128054

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_RegMaxA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (ξ : Fin n → ℂ) : Complex.I • rmVec ξ = ∑ j, (Complex.I * ξ j) • bas n j := by
  unfold rmVec
  rw [Finset.smul_sum]
  simp_rw [smul_smul]
end ReciprocityTheory.L2DbarEstimates.Y
