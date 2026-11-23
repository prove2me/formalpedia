-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Ck.mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:27:41.894637+00:00
-- url     : https://prove2.me/submissions/fe35a3db-354b-4c86-86cf-ffc06e7b03d4

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq

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
namespace Ck
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k l : ℕ) (hkl : k ≤ l)
    (f : M → ℂ) (hf : Ck n z l f) : Ck n z k f := by
  intro e he
  exact (hf e he).of_le (by exact_mod_cast hkl)
end Ck
end ReciprocityTheory.L2DbarEstimates
