-- Prove2me | solution 1 for ValuationSubring.exists_ne_zero_and_v_le_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b1beaa3a-8cb0-53ad-a53c-69105d71eefe

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_ne_zero_and_v_le_of_liesOverPrime

set_option autoImplicit false

theorem solution
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ε : A.ValueGroup) (hε : ε ≠ 0) :
    ∃ y : A.valuation.Completion, y ≠ 0 ∧ Valued.v y ≤ ε := by
  obtain ⟨x, hx⟩ := A.valuation_surjective ε
  refine ⟨((WithVal.toVal A.valuation x : WithVal A.valuation) : A.valuation.Completion), ?_, ?_⟩
  · intro h
    apply hε
    have := congrArg (Valued.v (R := A.valuation.Completion)) h
    rw [Valued.valuedCompletion_apply, WithVal.valued_toVal, hx, map_zero] at this
    exact this
  · rw [Valued.valuedCompletion_apply, WithVal.valued_toVal, hx]

end S_ValuationSubring_exists_ne_zero_and_v_le_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_exists_ne_zero_and_v_le_of_liesOverPrime (solution)
