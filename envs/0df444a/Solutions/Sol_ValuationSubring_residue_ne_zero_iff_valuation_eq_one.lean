-- Prove2me | solution 1 for ValuationSubring.residue_ne_zero_iff_valuation_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/abc75de5-84ff-528e-8aca-7af9318de7d1

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_residue_ne_zero_iff_valuation_eq_one

set_option autoImplicit false

theorem solution {K : Type*} [Field K] (A : ValuationSubring K) {a : K} (ha : a ∈ A) :
    IsLocalRing.residue A ⟨a, ha⟩ ≠ 0 ↔ A.valuation a = 1 := by
  rw [IsLocalRing.residue_ne_zero_iff_isUnit, A.valuation_eq_one_iff]

end S_ValuationSubring_residue_ne_zero_iff_valuation_eq_one
end P2MW
export P2MW.S_ValuationSubring_residue_ne_zero_iff_valuation_eq_one (solution)
