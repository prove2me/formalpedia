-- Prove2me | solution 1 for ValuationSubring.residue_eq_residue_iff_valuation_sub_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/7c6bec1d-46d4-5f8f-b50b-6cde680ae68d

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ValuationSubring_residue_eq_residue_iff_valuation_sub_lt_one

set_option autoImplicit false

theorem solution {K : Type*} [Field K] (A : ValuationSubring K) {a b : K} (ha : a ∈ A) (hb : b ∈ A) :
    IsLocalRing.residue A ⟨a, ha⟩ = IsLocalRing.residue A ⟨b, hb⟩ ↔ A.valuation (a - b) < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
  rfl

end S_ValuationSubring_residue_eq_residue_iff_valuation_sub_lt_one
end P2MW
export P2MW.S_ValuationSubring_residue_eq_residue_iff_valuation_sub_lt_one (solution)
