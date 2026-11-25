-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ordMod_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:35:08.282796+00:00
-- url     : https://prove2.me/submissions/25499c33-1e3c-4fe5-9cec-f6bbc9170fe2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_HeightOneIffDimOne
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_ord_ringEquiv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_quotQuotComapEquiv_mk

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
theorem _root_.solution (a b : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    ordMod P (Ideal.Quotient.mk (Ideal.span {a}) b) =
      ordMod (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {a})) P) b := by
  unfold ordMod
  rw [ord_ringEquiv (quotQuotComapEquiv a P), quotQuotComapEquiv_mk]
end ReciprocityTheory.ChartRestriction.G.AI
