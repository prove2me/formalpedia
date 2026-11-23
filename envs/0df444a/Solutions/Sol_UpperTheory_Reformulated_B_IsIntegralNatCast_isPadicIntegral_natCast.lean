-- Prove2me | solution 1 for UpperTheory.Reformulated.B.IsIntegralNatCast.isPadicIntegral_natCast
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:03.791923+00:00
-- url     : https://prove2.me/submissions/ac021abf-71a0-40cd-9839-c765bd617c3e

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IsIntegralNatCast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.IsIntegralNatCast
theorem _root_.solution :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (n : ℕ), UpperTheory.Reformulated.B.IsIntegralNatCast.IsIntP (↑n : ℂ_[p]) := by
  intro p _ n
  exact IsUltrametricDist.norm_natCast_le_one ℂ_[p] n
end UpperTheory.Reformulated.B.IsIntegralNatCast
