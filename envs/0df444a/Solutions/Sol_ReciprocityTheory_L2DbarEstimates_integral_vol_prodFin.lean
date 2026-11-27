-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.integral_vol_prodFin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:29:50.78143+00:00
-- url     : https://prove2.me/submissions/4c6e94a2-02f7-482d-b562-ccb0a31d0b1b

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
theorem _root_.solution {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (p : ℕ) (f : M × Fin p → ℂ) (hf : Integrable f (vol n (fun q : M × Fin p => z q.1))) :
    ∫ q, f q ∂vol n (fun q : M × Fin p => z q.1) = ∑ i, ∫ x, f (x, i) ∂vol n z := by
  rw [vol_prodFin_eq n z hz p] at hf ⊢
  rw [integral_finset_sum_measure (integrable_finset_sum_measure.1 hf)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_map (measurable_id.prodMk measurable_const).aemeasurable
    (integrable_finset_sum_measure.1 hf i (Finset.mem_univ _)).aestronglyMeasurable
end ReciprocityTheory.L2DbarEstimates
