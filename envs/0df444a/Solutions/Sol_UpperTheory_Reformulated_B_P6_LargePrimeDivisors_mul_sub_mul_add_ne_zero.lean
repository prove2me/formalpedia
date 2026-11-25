-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.LargePrimeDivisors.mul_sub_mul_add_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:47.355251+00:00
-- url     : https://prove2.me/submissions/55d5bb19-9535-45a9-a65d-bef8c3d8bc26

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
open Polynomial
namespace UpperTheory.Reformulated.B.P6.LargePrimeDivisors
theorem _root_.solution (f : Polynomial ℤ) (hf : 0 < f.natDegree) (c : ℤ) :
    f * (f - C c) * (f + C c) ≠ 0 := by
  have h1 : f ≠ 0 := by
    rintro rfl
    simp at hf
  have h2 : f - C c ≠ 0 := by
    intro h
    have h' : f = C c := sub_eq_zero.mp h
    rw [h', natDegree_C] at hf
    exact lt_irrefl _ hf
  have h3 : f + C c ≠ 0 := by
    intro h
    have h' : f = -C c := eq_neg_of_add_eq_zero_left h
    rw [h', natDegree_neg, natDegree_C] at hf
    exact lt_irrefl _ hf
  exact mul_ne_zero (mul_ne_zero h1 h2) h3
end UpperTheory.Reformulated.B.P6.LargePrimeDivisors
