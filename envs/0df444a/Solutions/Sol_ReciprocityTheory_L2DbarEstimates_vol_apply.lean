-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.vol_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:41:33.999869+00:00
-- url     : https://prove2.me/submissions/ff10d59c-eea0-4b57-b72c-cae50e324411

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_volAdditive

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
theorem _root_.solution {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (A : Set M) (hA : MeasurableSet A) :
    vol n z A = volFun n z A := by
  rw [vol, dif_pos (volAdditive n z hz), Measure.ofMeasurable_apply A hA]
end ReciprocityTheory.L2DbarEstimates
