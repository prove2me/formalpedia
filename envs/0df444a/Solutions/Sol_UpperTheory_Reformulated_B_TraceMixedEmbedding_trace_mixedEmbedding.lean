-- Prove2me | solution 1 for UpperTheory.Reformulated.B.TraceMixedEmbedding.trace_mixedEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:46:37.445319+00:00
-- url     : https://prove2.me/submissions/cc0b7845-17a1-4fec-b7df-fd9128b7b1d5

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_TraceMixedEmbedding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.TraceMixedEmbedding
theorem _root_.solution :
    ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] (y : F),
    (Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace F) : NumberField.mixedEmbedding.mixedSpace F → ℝ)
        ((NumberField.mixedEmbedding F : F → NumberField.mixedEmbedding.mixedSpace F) y) =
      (↑((Algebra.trace ℚ F : F → ℚ) y) : ℝ) := by
  intro F _ _ y
  classical
  rw [Algebra.trace_eq_matrix_trace (NumberField.mixedEmbedding.latticeBasis F),
    Algebra.trace_eq_matrix_trace (NumberField.integralBasis F)]
  simp only [Matrix.trace, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Rat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [NumberField.mixedEmbedding.latticeBasis_apply, ← map_mul,
    NumberField.mixedEmbedding.latticeBasis_repr_apply]
end UpperTheory.Reformulated.B.TraceMixedEmbedding
