-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_CommonMajorizingLattice_majLattice_common__06b6d465f20d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:03:41.283814+00:00
-- url     : https://prove2.me/submissions/6d71ec51-c4b0-421d-b939-4867b78d5760

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CommonMajorizingLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.CommonMajorizingLattice
theorem _root_.solution.{u_1} :
    ∀ {K : Type u_1} [inst : Field K] [NumberField K] (t : Finset K),
    ∃ (d : ℤ), d ≠ (0 : ℤ) ∧ ∀ a ∈ t, IsIntegral ℤ ((↑d : K) * a) := by
  intro K _ _ t
  obtain ⟨d, hd, h⟩ := exists_integral_multiples ℤ ℚ t
  exact ⟨d, hd, fun a ha => by simpa [zsmul_eq_mul] using h a ha⟩
end UpperTheory.Reformulated.B.CommonMajorizingLattice
