-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Smooth.normSq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:32.117903+00:00
-- url     : https://prove2.me/submissions/a30c91f4-5260-40ed-86f1-8a9a7dea5ccb

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_mul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_conj

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
namespace Smooth
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (f : M → ℂ) (hf : Smooth n z f) :
    SmoothR n z (fun x => ‖f x‖ ^ 2) := by
  intro e he
  have h1 := (Smooth.mul n z f _ hf (Smooth.conj n z f hf)) e he
  refine h1.congr (fun w _ => ?_)
  simp only [Function.comp_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
end Smooth
end ReciprocityTheory.L2DbarEstimates
