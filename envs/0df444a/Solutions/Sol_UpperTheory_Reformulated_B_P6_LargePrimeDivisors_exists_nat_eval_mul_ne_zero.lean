-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.LargePrimeDivisors.exists_nat_eval_mul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:48:50.388815+00:00
-- url     : https://prove2.me/submissions/1b156102-53b6-428d-ac46-ce8f71165dea

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_LargePrimeDivisors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.LargePrimeDivisors
open scoped Int LT OfNat Polynomial Dvd
namespace UpperTheory.Reformulated.B.P6.LargePrimeDivisors
theorem _root_.solution (P : Polynomial ℤ) (hP : P ≠ 0) (a : ℤ) (ha : a ≠ 0) :
    ∃ t : ℕ, P.eval (a * (t : ℤ)) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := fun t : ℕ => a * (t : ℤ))
  · intro x y hxy
    have h2 : (x : ℤ) = (y : ℤ) := mul_left_cancel₀ ha hxy
    exact_mod_cast h2
  · intro t
    exact h t
end UpperTheory.Reformulated.B.P6.LargePrimeDivisors
