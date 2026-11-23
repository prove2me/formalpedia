-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.CkR.comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:23:53.11045+00:00
-- url     : https://prove2.me/submissions/210ca03c-4d9e-44ec-a316-c8f5469c855f

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
namespace CkR
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (φ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (f : M → ℝ) (hf : CkR n z k f) :
    CkR n z k (fun x => φ (f x)) := by
  intro e he
  have h1 := Complex.reCLM.contDiff.comp_contDiffOn (hf e he)
  have h2 := Complex.ofRealCLM.contDiff.comp_contDiffOn
    ((hφ.of_le (by exact_mod_cast le_top)).comp_contDiffOn h1)
  refine h2.congr (fun w _ => ?_)
  simp
end CkR
end ReciprocityTheory.L2DbarEstimates
