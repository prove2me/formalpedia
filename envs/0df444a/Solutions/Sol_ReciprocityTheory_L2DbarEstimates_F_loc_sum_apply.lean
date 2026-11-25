-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.loc_sum_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:28:53.929176+00:00
-- url     : https://prove2.me/submissions/7d6f6e0e-4092-45d1-8e2c-e32c9c448da9

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA

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
theorem _root_.solution {n N : ℕ} (a : Fin N → V n) (j : Fin n) :
    (∑ i, a i) j = ∑ i, a i j := by
  first
  | exact Finset.sum_apply j Finset.univ a
  | simp [Finset.sum_apply]
  | simp [WithLp.ofLp_sum]
  | exact map_sum (EuclideanSpace.proj (𝕜 := ℂ) j) a Finset.univ
  | simpa using map_sum (EuclideanSpace.proj (𝕜 := ℂ) j) a Finset.univ
end ReciprocityTheory.L2DbarEstimates.F
