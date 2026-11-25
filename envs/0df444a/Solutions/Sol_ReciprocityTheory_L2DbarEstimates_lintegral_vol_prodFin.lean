-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.lintegral_vol_prodFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:16:26.27483+00:00
-- url     : https://prove2.me/submissions/656d16b7-d000-44a0-8751-b0a1ffb009e7

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IsLocalHomeomorphCompFst
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_prodFin_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (f : M × Fin p → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, f q ∂vol n (fun q : M × Fin p => z q.1) = ∑ i, ∫⁻ x, f (x, i) ∂vol n z := by
  rw [vol_prodFin_eq n z hz p, lintegral_finset_sum_measure]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact lintegral_map hf (measurable_id.prodMk measurable_const)
end ReciprocityTheory.L2DbarEstimates
