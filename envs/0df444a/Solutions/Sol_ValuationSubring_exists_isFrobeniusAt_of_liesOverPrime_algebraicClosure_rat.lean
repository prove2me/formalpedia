-- Prove2me | solution 1 for ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/0e651b9f-a1be-5b4c-aff9-4a45a1018788

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat

set_option autoImplicit false

theorem solution
    {p : ℕ} (hp : p.Prime) {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime p) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p :=
  ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hp A hA

end S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat
end P2MW
export P2MW.S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat (solution)
