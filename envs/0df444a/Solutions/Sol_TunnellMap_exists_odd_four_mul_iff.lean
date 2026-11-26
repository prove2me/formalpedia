-- Prove2me | solution 1 for TunnellMap.exists_odd_four_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:20:04.326836+00:00
-- url     : https://prove2.me/submissions/710ded3e-f2f4-4c35-94bb-2a792ab8cfb8

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (a : ℤ) :
    (∃ q : ℤ, Odd q ∧ a = 4 * q) ↔ a % 8 = 4 := by
  constructor
  · rintro ⟨q, ⟨k, hk⟩, ha⟩
    subst hk
    omega
  · intro ha
    refine ⟨2 * (a / 8) + 1, ⟨a / 8, by ring⟩, ?_⟩
    omega
end TunnellMap
