-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.flA_apply_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:19:23.919167+00:00
-- url     : https://prove2.me/submissions/2e4712cb-7280-4329-91b5-1b234c51c299

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLocA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_flA_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (D : V n →L[ℂ] V n) (ξ : Fin n → ℂ) (a : Fin n) :
    D (WithLp.toLp 2 ξ) a = ∑ j, ξ j * D (bas n j) a := by
  conv_lhs => rw [flA_expand (WithLp.toLp 2 ξ)]
  simp [map_sum, map_smul]
end ReciprocityTheory.L2DbarEstimates.Y
