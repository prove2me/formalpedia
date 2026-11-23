-- Prove2me | solution 1 for PI.CntNotIntW.trace_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:16:59.415733+00:00
-- url     : https://prove2.me/submissions/e58f024a-3242-49fd-aaf6-4acabbc522e9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CountNonIntegrality_TraceOfKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.CntNotIntW
open scoped TensorProduct
namespace PI.CntNotIntW
theorem _root_.solution {Q K : Type*} [Field Q] [Algebra ℚ Q] [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
    (y : K) : Algebra.trace Q (Q ⊗[ℚ] K) (1 ⊗ₜ y) = algebraMap ℚ Q (Algebra.trace ℚ K y) := by
  rw [Algebra.trace_apply, Algebra.trace_apply]
  have h : Algebra.lmul Q (Q ⊗[ℚ] K) (1 ⊗ₜ y) = (Algebra.lmul ℚ K y).baseChange Q := by
    ext k
    simp
  rw [h, LinearMap.trace_baseChange]
end PI.CntNotIntW
