-- Prove2me | solution 1 for UpperTheory.Reformulated.B.CapelliMiscellany.norm_natCast_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:34.860224+00:00
-- url     : https://prove2.me/submissions/480d7b47-4651-4b29-a88d-5d66080ee00e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_NormNatCastPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.CapelliMiscellany
theorem _root_.solution :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)], ‖(↑p : PadicAlgCl p)‖ = (↑p : ℝ)⁻¹ := by
  intro p _
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p]
  exact (PadicAlgCl.norm_extends p (p : ℚ_[p])).trans Padic.norm_p
end UpperTheory.Reformulated.B.CapelliMiscellany
