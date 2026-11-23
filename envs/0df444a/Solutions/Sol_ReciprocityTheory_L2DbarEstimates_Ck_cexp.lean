-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Ck.cexp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:29.461976+00:00
-- url     : https://prove2.me/submissions/c61bb7ed-ad30-4815-90a8-c8c6d2099979

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
namespace Ck
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) (f : M → ℂ) (hf : Ck n z k f) :
    Ck n z k (fun x => Complex.exp (f x)) := by
  intro e he
  exact Complex.contDiff_exp.comp_contDiffOn (hf e he)
end Ck
end ReciprocityTheory.L2DbarEstimates
