-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:35:33.746951+00:00
-- url     : https://prove2.me/submissions/a0bc5052-e531-42ac-a478-4b4144eb06fd

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InPApplyEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qh16
theorem _root_.solution :
    ∀ {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ},
      UpperTheory.Reformulated.B.Qh16.inP ε X → ∀ {a b : Fin n}, ε a = ε b → X a b = (0 : ℂ) := by
  intro n ε X h a b hab
  have h1 := congrFun (congrFun h.2 a) b
  unfold UpperTheory.Reformulated.B.Qh16.Jm at h1
  rw [Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hab] at h1
  split_ifs at h1
  · linear_combination (1 / 2 : ℂ) * h1
  · linear_combination (-1 / 2 : ℂ) * h1
end UpperTheory.Reformulated.B.Qh16
