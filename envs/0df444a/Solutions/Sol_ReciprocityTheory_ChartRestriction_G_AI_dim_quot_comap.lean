-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.dim_quot_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:27:37.044008+00:00
-- url     : https://prove2.me/submissions/5cb49f93-44fa-4cfd-bcac-fc67d4308aec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_HeightOneIffDimOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module
universe u v
variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (a : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    ringKrullDim ((A ⧸ Ideal.span {a}) ⧸ P.asIdeal) =
      ringKrullDim (A ⧸ (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P).asIdeal) := by
  first
    | exact ringKrullDim_eq_of_ringEquiv (quotQuotComapEquiv a P)
    | exact (quotQuotComapEquiv a P).ringKrullDim
    | exact RingEquiv.ringKrullDim (quotQuotComapEquiv a P)
end ReciprocityTheory.ChartRestriction.G.AI
