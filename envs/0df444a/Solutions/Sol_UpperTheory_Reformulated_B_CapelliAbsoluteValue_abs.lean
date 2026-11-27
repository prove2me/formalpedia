-- Prove2me | solution 1 for UpperTheory.Reformulated.B.CapelliAbsoluteValue.abs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:33:51.382585+00:00
-- url     : https://prove2.me/submissions/bef7d922-334c-4722-9e47-6ac8fd700ce9

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfiniteNormOneElements
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_AbsoluteValueAltAlt
import Theorems.Thm_UpperTheory_infinite_norm_one_elements


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.CapelliAbsoluteValue
theorem _root_.solution : ∀ {F E : Type} [CommSemiring F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  NumberField.IsTotallyComplex E → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
    {t : E | t * σ t = 1}.Infinite :=
  UpperTheory.infinite_norm_one_elements
end UpperTheory.Reformulated.B.CapelliAbsoluteValue
