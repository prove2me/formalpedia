-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.evl_smoothR_sumSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:23:43.074872+00:00
-- url     : https://prove2.me/submissions/03f2ba43-15d7-4bd9-b7b7-a4c3f0a75747

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EvLeviA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Holo_smooth
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_normSq
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_smoothR_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open scoped ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (g : ι → M → ℂ) (hg : ∀ i, Holo n z (g i)) :
    SmoothR n z (fun y => ∑ i ∈ s, ‖g i y‖ ^ 2) :=
  smoothR_sum n z s (fun i y => ‖g i y‖ ^ 2) fun i _ => Smooth.normSq n z _ (Holo.smooth n z _ (hg i))
end ReciprocityTheory.L2DbarEstimates.I
