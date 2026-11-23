-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qh23.uniA_mul_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:17.602288+00:00
-- url     : https://prove2.me/submissions/6d94b73c-df0d-44bb-9f57-9fa25253a7a8

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UniAMulDiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qh23
theorem _root_.solution :
    ∀ {F : Type} [inst : Field F] {k : ℕ} (A B : Matrix (Fin k) (Fin k) F),
    A.BlockTriangular id → B.BlockTriangular id → ∀ (i : Fin k), (A * B) i i = A i i * B i i := by
  intro F _ k A B hA hB i
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single i (fun j _ hj => ?_) (fun h => absurd (Finset.mem_univ i) h)
  rcases lt_or_gt_of_ne hj with h | h
  · rw [hA (show id j < id i from h), zero_mul]
  · rw [hB (show id i < id j from h), mul_zero]
end UpperTheory.Reformulated.B.Qh23
