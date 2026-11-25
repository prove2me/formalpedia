-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.lse_smoothR_iff_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:43:38.024395+00:00
-- url     : https://prove2.me/submissions/9da411c5-d62e-4c8a-af46-ea2033042957

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_NormFibrations_LseSmoothRIffReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open Filter Topology
open scoped ContDiff
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℝ) :
    SmoothR n z f ↔ ∀ e : OpenPartialHomeomorph M (V n), IsChart n z e →
      ContDiffOn ℝ ∞ (f ∘ e.symm) e.target := by
  unfold SmoothR Smooth
  refine forall_congr' fun e => imp_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · have h1 := Complex.reCLM.contDiff.comp_contDiffOn h
    simpa [Function.comp_def, Complex.reCLM_apply] using h1
  · exact Complex.ofRealCLM.contDiff.comp_contDiffOn h
end ReciprocityTheory.L2DbarEstimates
