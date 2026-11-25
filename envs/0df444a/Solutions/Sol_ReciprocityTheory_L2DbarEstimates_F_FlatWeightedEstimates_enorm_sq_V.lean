-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.enorm_sq_V
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:02:44.360583+00:00
-- url     : https://prove2.me/submissions/4f035dd6-c1a4-45e5-9438-217cfd70a451

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd

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
open ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
namespace ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
theorem _root_.solution {n : ℕ} (x : V n) : ‖x‖ₑ ^ 2 = ∑ j, ‖x j‖ₑ ^ 2 := by
  simp only [← ofReal_norm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _), EuclideanSpace.norm_sq_eq,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
  exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_pow (norm_nonneg _) 2
end ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
