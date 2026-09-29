-- Prove2me | solution 1 for Polynomial.finite_setOf_criticalValue
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/ebddbbb4-0e97-553a-8580-25b3800fde01

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_finite_setOf_criticalValue

set_option autoImplicit false

open Polynomial

universe u

theorem solution
    {k : Type u} [Field k] (P : k[X]) (hP : derivative P ≠ 0) :
    {c : k | ∃ x : k, P.eval x = c ∧ (derivative P).eval x = 0}.Finite := by
  have hfin : {x : k | (derivative P).eval x = 0}.Finite := (derivative P).finite_setOf_isRoot hP
  refine (hfin.image fun x => P.eval x).subset ?_
  rintro c ⟨x, rfl, hx⟩
  exact ⟨x, hx, rfl⟩

end S_Polynomial_finite_setOf_criticalValue
end P2MW
export P2MW.S_Polynomial_finite_setOf_criticalValue (solution)
