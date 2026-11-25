-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.localExtension_eq_zero_off
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:17:57.190005+00:00
-- url     : https://prove2.me/submissions/480515a7-d012-4137-a98e-eb475e82abc6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LocalExtensionEqMulJacobian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (g : Fin n → M → ℂ) (c : M → ℂ) (W : M → Set M) {x : M}
    (hx : ∀ p ∈ zeroSet n g, x ∉ W p) : gt n z g c W x = 0 := by
  unfold gt
  exact finsum_mem_eq_zero_of_forall_eq_zero (fun p hp => Set.indicator_of_notMem (hx p hp) _)
end ReciprocityTheory.L2DbarEstimates.I
