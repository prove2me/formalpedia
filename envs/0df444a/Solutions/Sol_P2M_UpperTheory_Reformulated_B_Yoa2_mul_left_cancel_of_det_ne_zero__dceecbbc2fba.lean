-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Yoa2_mul_left_cancel_of_det_ne_zero__dceecbbc2fba
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:01:35.547451+00:00
-- url     : https://prove2.me/submissions/8e539504-e190-4f69-8250-49434e6cd460

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulLeftCancelOfDetNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Yoa2.mul_left_cancel_of_det_ne_zero
theorem _root_.solution.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] [IsDomain R] {n : ℕ} {A X Y : Matrix (Fin n) (Fin n) R},
      A.det ≠ (0 : R) → A * X = A * Y → X = Y := by
  intro R _ _ n A X Y hA h
  have h2 : A.det • X = A.det • Y := by
    have h3 : A.adjugate * (A * X) = A.adjugate * (A * Y) := by rw [h]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul] at h3
    exact h3
  ext i j
  have h4 : A.det * X i j = A.det * Y i j := congrFun (congrFun h2 i) j
  exact mul_left_cancel₀ hA h4
end UpperTheory.Reformulated.B.Yoa2.mul_left_cancel_of_det_ne_zero
