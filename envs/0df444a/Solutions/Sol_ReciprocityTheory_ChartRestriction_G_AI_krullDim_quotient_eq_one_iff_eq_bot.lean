-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.krullDim_quotient_eq_one_iff_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:28:18.614168+00:00
-- url     : https://prove2.me/submissions/d1d90969-4563-4f92-9868-5627f60af5b1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LengthCokerEqKerAddDimOneOrderSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_KrullDimQuotientEqOneIffEqBot

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
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
namespace ReciprocityTheory.ChartRestriction.G.AI
theorem _root_.solution [Ring.KrullDimLE 1 A] (h : ringKrullDim A = 1) (p : PrimeSpectrum A) :
    ringKrullDim (A ⧸ p.asIdeal) = 1 ↔ p.asIdeal = ⊥ := by
  constructor
  · intro hq
    by_contra hne
    have hmax : p.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal_of_ne_bot p.isPrime hne
    have h0 := ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
    rw [h0] at hq
    exact zero_ne_one hq
  · intro hp
    rw [ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hp).trans (RingEquiv.quotientBot A)), h]
end ReciprocityTheory.ChartRestriction.G.AI
