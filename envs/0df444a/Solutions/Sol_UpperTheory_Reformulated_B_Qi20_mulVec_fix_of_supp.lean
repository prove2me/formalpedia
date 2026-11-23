-- Prove2me | solution 1 for UpperTheory.Reformulated.B.Qi20.mulVec_fix_of_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:37:39.113184+00:00
-- url     : https://prove2.me/submissions/66cca50b-1f71-4b93-af47-d2b249048d25

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulVecFixOfSupp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qi20
theorem _root_.solution :
    ∀ {m : ℕ} (y : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ),
    (∀ (j : Fin m), v j ≠ (0 : ℂ) → ∀ (i : Fin m), y i j = if i = j then (1 : ℂ) else (0 : ℂ)) → y.mulVec v = v := by
  intro m y v h
  have key : y.mulVec v = (1 : Matrix (Fin m) (Fin m) ℂ).mulVec v := by
    funext i
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : v j = 0
    · rw [hj, mul_zero, mul_zero]
    · rw [h j hj i, Matrix.one_apply]
  rw [key, Matrix.one_mulVec]
end UpperTheory.Reformulated.B.Qi20
