-- Prove2me | solution 1 for Reformulated.AlgebraicInfinityType.InfinityType.exponents_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:31:29.497354+00:00
-- url     : https://prove2.me/submissions/31143f29-ee09-44e1-bf27-2d3b48b6303b

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_AlgebraicInfinityType_InfinityType

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Reformulated Reformulated.AlgebraicInfinityType
open NumberField
open Reformulated.AlgebraicInfinityType.InfinityType
variable {F : Type*} [Field F] {n : ℕ}
namespace Reformulated.AlgebraicInfinityType.InfinityType
theorem _root_.solution (t : InfinityType F n) (σ : F →+* ℂ) :
    t.exponents (ComplexEmbedding.conjugate σ) = (t.pairs σ).map Prod.snd := by
  simp [exponents, t.pairs_conjugate]
end Reformulated.AlgebraicInfinityType.InfinityType
