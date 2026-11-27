-- Prove2me | solution 1 for UpperTheory.V.AlgebraTools.IsCplAt.isPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:34:11.221784+00:00
-- url     : https://prove2.me/submissions/a03a3a81-ee66-4e65-94ec-f3285ce75229

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_AlgebraTools_IsCplAtSelf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open UpperTheory UpperTheory.V UpperTheory.V.AlgebraTools
namespace UpperTheory.V.AlgebraTools
namespace IsCplAt
theorem _root_.solution {R : Type} [CommRing R] {p : Ideal R} {B : Type} [CommRing B]
    [IsLocalRing B] [Algebra R B] (h : IsCplAt R p B) : p.IsPrime := by
  rw [← h.comap_eq]
  exact Ideal.comap_isPrime _ _
end IsCplAt
end UpperTheory.V.AlgebraTools
