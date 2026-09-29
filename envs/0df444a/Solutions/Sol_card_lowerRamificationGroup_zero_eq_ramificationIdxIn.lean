-- Prove2me | solution 1 for card_lowerRamificationGroup_zero_eq_ramificationIdxIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/7019e6df-f472-5fe1-b66f-c63f67d1899d

import Definitions.Def_DifferentFiltrationFormula
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_Compat_Mathlib430
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn



theorem solution {A : Type*} [CommRing A] [IsLocalRing A]
    {B : Type*} [CommRing B] [IsDedekindDomain B] [IsLocalRing B]
    [Algebra A B] [Module.IsTorsionFree A B]
    {G : Type*} [Group G] [MulSemiringAction G B]
    [IsDedekindDomain A] [Module.Finite A B] [IsGaloisGroup G A B] [Finite G]
    [(IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A)]
    [Algebra.IsSeparable (A ⧸ IsLocalRing.maximalIdeal A) (B ⧸ IsLocalRing.maximalIdeal B)]
    (hp : IsLocalRing.maximalIdeal A ≠ ⊥) :
    Nat.card (IsLocalRing.lowerRamificationGroup B G 0)
      = (IsLocalRing.maximalIdeal A).ramificationIdxIn B := by
  rw [IsLocalRing.lowerRamificationGroup_zero_eq_inertia]
  exact Ideal.card_inertia_eq_ramificationIdxIn' (IsLocalRing.maximalIdeal A) hp
    (IsLocalRing.maximalIdeal B)

end S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn
end P2MW
export P2MW.S_card_lowerRamificationGroup_zero_eq_ramificationIdxIn (solution)
