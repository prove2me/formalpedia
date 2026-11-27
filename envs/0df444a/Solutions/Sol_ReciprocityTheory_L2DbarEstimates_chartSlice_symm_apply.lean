-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.chartSlice_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:31:19.14993+00:00
-- url     : https://prove2.me/submissions/9e071370-c885-4c3c-a37c-734443b9743a

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IsLocalHomeomorphCompFst

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
theorem _root_.solution {M : Type*} [TopologicalSpace M] {n : ℕ}
    (e : OpenPartialHomeomorph M (V n)) {p : ℕ} (i : Fin p) (y : V n) :
    (chartSlice e i).symm y = (e.symm y, i) := rfl
end ReciprocityTheory.L2DbarEstimates
