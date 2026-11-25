-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.dbar_sq_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:09:10.009002+00:00
-- url     : https://prove2.me/submissions/dd4d3e90-e925-4fb9-b565-5ff9bceb9d5a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_DerivSmoothTransitionOfOneLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (u : M → ℂ) (x : M) : 0 ≤ dbarSq n z u x := by
  unfold dbarSq
  exact Finset.sum_nonneg fun j _ => by positivity
end ReciprocityTheory.L2DbarEstimates.F
