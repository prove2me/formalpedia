-- Prove2me | solution 1 for TunnellMap.exists_odd_two_mul_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:20:15.516368+00:00
-- url     : https://prove2.me/submissions/e2d8425a-3c7e-4b27-9688-37b5bb0972b7

import Definitions.Def_TunnellMap_OrbitRanking
import Definitions.Def_TunnellMap_ResidualTargetTest

set_option autoImplicit true
open TunnellMap
namespace TunnellMap
theorem _root_.solution (a : ℤ) :
    (∃ q : ℤ, Odd q ∧ a = 2 * q) ↔ a % 4 = 2 := by
  constructor
  · rintro ⟨q, ⟨k, hk⟩, ha⟩
    subst hk
    omega
  · intro ha
    refine ⟨2 * (a / 4) + 1, ⟨a / 4, by ring⟩, ?_⟩
    omega
end TunnellMap
