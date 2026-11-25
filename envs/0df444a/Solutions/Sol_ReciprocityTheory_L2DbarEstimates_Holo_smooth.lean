-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Holo.smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:15:06.530853+00:00
-- url     : https://prove2.me/submissions/82dac21f-fcf2-47b9-987e-3f5bb76e5172

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
namespace Holo
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ)
    (hf : Holo n z f) : Smooth n z f := by
  intro e he
  exact (contDiffOn_of_differentiableOn n _ _ e.open_target (hf e he)).restrict_scalars ℝ
end Holo
end ReciprocityTheory.L2DbarEstimates
