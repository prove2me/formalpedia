-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Ck.re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:58.712022+00:00
-- url     : https://prove2.me/submissions/69b61fa9-a3a7-4255-82a5-ad01d375f9d8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set ChartWirtingerDerivatives
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
namespace Ck
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℂ) (hf : Ck n z k f) :
    CkR n z k (fun x => (f x).re) := by
  intro e he
  have h1 := (Complex.ofRealCLM.comp Complex.reCLM).contDiff.comp_contDiffOn (hf e he)
  refine h1.congr (fun w _ => ?_)
  simp
end Ck
end ReciprocityTheory.L2DbarEstimates
