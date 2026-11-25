-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.chT_aesm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:23:12.520104+00:00
-- url     : https://prove2.me/submissions/b710ece1-0355-4d2d-b0cf-ad8dc11e5ad4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_ChartA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_chT_aem_symm
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_restrict_source


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set Function
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M]
  [BorelSpace M] {n : ℕ} {z : M → V n} {e : OpenPartialHomeomorph M (V n)}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] (hz : IsLocalHomeomorph z)
    (he : IsChart n z e) (f : M → E) (hf : AEStronglyMeasurable f (vol n z)) :
    AEStronglyMeasurable (e.target.indicator (f ∘ e.symm)) volume := by
  have hf' : AEStronglyMeasurable f (Measure.map e.symm (volume.restrict e.target)) := by
    rw [← vol_restrict_source n z hz e he]; exact hf.restrict
  exact (aestronglyMeasurable_indicator_iff e.open_target.measurableSet).2
    (hf'.comp_aemeasurable (chT_aem_symm (e := e)))
end ReciprocityTheory.L2DbarEstimates.F
