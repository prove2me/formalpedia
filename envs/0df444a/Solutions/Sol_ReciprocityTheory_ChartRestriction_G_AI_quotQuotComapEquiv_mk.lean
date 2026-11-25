-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.quotQuotComapEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:28:27.006447+00:00
-- url     : https://prove2.me/submissions/f3ddc059-f5af-485a-8ae7-862658632b4d

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
variable {A : Type u} [CommRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution (a b : A) (P : PrimeSpectrum (A ⧸ Ideal.span {a})) :
    quotQuotComapEquiv a P (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ b)) =
      Ideal.Quotient.mk _ b := by
  first
    | rfl
    | simp [quotQuotComapEquiv]
    | fail
end ReciprocityTheory.ChartRestriction.G.AI
