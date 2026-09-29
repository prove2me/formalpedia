-- Prove2me | solution 1 for ValuationSubring.not_countable_upperHalfPlane_ratClosure_completion_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/4b5ccd91-471d-5fc7-97c3-4926e7db5a57

import Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane
import Definitions.Def_ValuationSubring_CompletionRatClosure
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_two_closed_subfields_completion_inf_eq_ratClosure_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_not_countable_upperHalfPlane_ratClosure_completion_of_liesOverPrime

set_option autoImplicit false

open ValuationSubring CerednikDrinfeld

theorem solution
    (r : ℕ) [Fact r.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime r) :
    ¬ (Omega.upperHalfPlane ↥(ratClosure A) A.valuation.Completion).Countable := by
  obtain ⟨L₁, L₂, -, -, -, -, -, hu₁, -⟩ :=
    ValuationSubring.exists_two_closed_subfields_completion_inf_eq_ratClosure_of_liesOverPrime r A hA
  intro h
  apply hu₁
  refine h.mono ?_
  rintro z ⟨-, hz⟩
  rw [Omega.mem_upperHalfPlane_iff]
  rintro ⟨x, hx⟩ rfl
  exact hz hx

end S_ValuationSubring_not_countable_upperHalfPlane_ratClosure_completion_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_not_countable_upperHalfPlane_ratClosure_completion_of_liesOverPrime (solution)
