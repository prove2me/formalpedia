-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.vol_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:57:26.25216+00:00
-- url     : https://prove2.me/submissions/10ba01ff-a678-440c-887e-17a12f6baccf

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_measurableSet_image_of_isLocalHomeomorph
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_encard_inter_fiber_of_injOn
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_vol_apply
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_mono


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
theorem _root_.solution {M : Type*} [TopologicalSpace M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (U : Set M) (hU : IsOpen U) (hinj : InjOn z U) (A : Set M) (hA : MeasurableSet A) (hAU : A ⊆ U) :
    vol n z A = volume (z '' A) := by
  rw [vol_apply n z hz A hA, volFun]
  have hinjA : InjOn z A := hinj.mono hAU
  simp_rw [encard_inter_fiber_of_injOn n z A hinjA]
  rw [lintegral_indicator_one (measurableSet_image_of_isLocalHomeomorph n z hz A hA)]
end ReciprocityTheory.L2DbarEstimates
