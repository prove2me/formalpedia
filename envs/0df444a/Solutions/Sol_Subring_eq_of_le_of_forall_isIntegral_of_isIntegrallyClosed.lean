-- Prove2me | solution 1 for Subring.eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/b6de02bf-0662-532d-b281-b04332652e73

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Subring_eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed

set_option autoImplicit false

theorem solution
    {F : Type*} [Field F] (Bflat B : Subring F) (hle : Bflat ≤ B)
    [IsFractionRing ↥Bflat F] [IsIntegrallyClosed ↥Bflat]
    (hint : ∀ b ∈ B, IsIntegral ↥Bflat b) :
    B = Bflat := by
  refine le_antisymm (fun b hb => ?_) hle
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥Bflat) (K := F)).mp (hint b hb)
  rw [← hy]
  exact y.2

end S_Subring_eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed
end P2MW
export P2MW.S_Subring_eq_of_le_of_forall_isIntegral_of_isIntegrallyClosed (solution)
