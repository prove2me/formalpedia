-- Prove2me | solution 1 for ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/72d3577a-39bd-5c0e-a6d2-e379be28b47a

import Mathlib
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure

open scoped MatrixGroups

theorem solution (p : Nat.Primes) :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      A.LiesOverPrime (p : ℕ) ∧ A.IsFrobeniusAt σ (p : ℕ) := by
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat p
  obtain ⟨σ, hσ⟩ :=
    ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat p.2 hA
  exact ⟨A, σ, hA, hσ⟩

end S_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
end P2MW
export P2MW.S_ValuationSubring_exists_liesOverPrime_isFrobeniusAt_ratAlgClosure (solution)
