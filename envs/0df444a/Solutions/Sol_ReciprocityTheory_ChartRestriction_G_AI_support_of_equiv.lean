-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.support_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:28:29.069288+00:00
-- url     : https://prove2.me/submissions/a6b99e21-553a-4eea-acfd-f5dc55638fae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthEqRangeAddRange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI
open Module PrimeSpectrum
open scoped Pointwise
universe u v
variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution {N : Type v} [AddCommGroup N] [Module A N] (q : PrimeSpectrum A)
    (e : N ≃ₗ[A] A ⧸ q.asIdeal) : support A N = zeroLocus (q.asIdeal : Set A) := by
  haveI : Module.Finite A N := Module.Finite.equiv e.symm
  rw [Module.support_eq_zeroLocus, e.annihilator_eq, Ideal.annihilator_quotient]
end ReciprocityTheory.ChartRestriction.G.AI
