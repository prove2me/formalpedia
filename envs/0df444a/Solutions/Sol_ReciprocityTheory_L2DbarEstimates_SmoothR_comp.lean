-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.SmoothR.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:23:50.596538+00:00
-- url     : https://prove2.me/submissions/934076de-41db-44ae-92df-ec9184720130

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset

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
namespace SmoothR
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℝ → ℝ) (hk : ContDiff ℝ ∞ k) (f : M → ℝ) (hf : SmoothR n z f) :
    SmoothR n z (fun x => k (f x)) := by
  intro e he
  have h1 := Complex.reCLM.contDiff.comp_contDiffOn (hf e he)
  have h2 := Complex.ofRealCLM.contDiff.comp_contDiffOn (hk.comp_contDiffOn h1)
  refine h2.congr (fun w _ => ?_)
  simp
end SmoothR
end ReciprocityTheory.L2DbarEstimates
