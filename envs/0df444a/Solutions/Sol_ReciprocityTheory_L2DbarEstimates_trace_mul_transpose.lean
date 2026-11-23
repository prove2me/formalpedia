-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.trace_mul_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:46.669689+00:00
-- url     : https://prove2.me/submissions/cc27f1f4-c488-4cdf-b7d5-19d97b341d8f

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_Matrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex ComplexConjugate
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {p : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {n : ℕ} (A V : Matrix (Fin p) (Fin n) ℂ) :
    trace (A * Vᵀ) = ∑ i, ∑ k, A i k * V i k := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]
end ReciprocityTheory.L2DbarEstimates
