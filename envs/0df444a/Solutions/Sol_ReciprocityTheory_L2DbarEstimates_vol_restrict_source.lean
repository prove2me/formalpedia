-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.vol_restrict_source
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:07:20.549861+00:00
-- url     : https://prove2.me/submissions/b986af7b-9c06-4528-a42d-68055afe991a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_injOn_source_of_chart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_image

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
theorem _root_.solution {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) :
    (vol n z).restrict e.source = Measure.map e.symm (volume.restrict e.target) := by
  ext B hB
  rw [Measure.restrict_apply hB,
    Measure.map_apply_of_aemeasurable
      (e.continuousOn_symm.aemeasurable e.open_target.measurableSet) hB,
    Measure.restrict_apply' e.open_target.measurableSet,
    vol_image n z hz e.source e.open_source (injOn_source_of_chart n z e he) _
      (hB.inter e.open_source.measurableSet) Set.inter_subset_right]
  congr 1
  rw [Set.image_congr (fun x hx => he hx.2), Set.inter_comm B e.source,
    e.image_source_inter_eq']
  exact Set.inter_comm _ _
end ReciprocityTheory.L2DbarEstimates
