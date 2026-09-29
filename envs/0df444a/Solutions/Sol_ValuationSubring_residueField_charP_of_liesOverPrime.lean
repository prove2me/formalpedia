-- Prove2me | solution 1 for ValuationSubring.residueField_charP_of_liesOverPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/d00fb876-463e-5b21-9b4b-d30e34be7c66

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_residueField_charP_of_liesOverPrime

theorem solution {L : Type*} [Field L]
    (A : ValuationSubring L) {ℓ : ℕ} (hℓ : ℓ.Prime) (hA : A.LiesOverPrime ℓ) :
    CharP (IsLocalRing.ResidueField A) ℓ := by
  refine (CharP.charP_iff_prime_eq_zero hℓ).mpr ?_
  rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff,
    ← ValuationSubring.coe_mem_nonunits_iff]
  have : (((ℓ : ℕ) : A) : L) = (ℓ : L) := by simp
  rw [this]
  exact hA

end S_ValuationSubring_residueField_charP_of_liesOverPrime
end P2MW
export P2MW.S_ValuationSubring_residueField_charP_of_liesOverPrime (solution)
