-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.ordQuotient_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:31:27.571345+00:00
-- url     : https://prove2.me/submissions/21b8d5d6-6cc7-49f7-9508-a5b58945e0c1

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
theorem _root_.solution (x : A) :
    ordMod ⟨⊥, Ideal.isPrime_bot⟩ x = Ring.ord A x := by
  unfold ordMod Ring.ord
  dsimp only
  have hs : Function.Surjective (algebraMap A (A ⧸ (⊥ : Ideal A))) := Ideal.Quotient.mk_surjective
  rw [← Module.length_eq_of_surjective hs]
  have h1 : Ideal.map (Ideal.Quotient.mkₐ A (⊥ : Ideal A)) (Ideal.span {x}) =
      Ideal.span {Ideal.Quotient.mk (⊥ : Ideal A) x} := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.Quotient.mkₐ_eq_mk]
  have e1 := (Ideal.quotientEquivAlgOfEq A h1).symm.trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ A ⊥ (Ideal.span {x})).trans
      (Ideal.quotientEquivAlgOfEq A (bot_sup_eq (Ideal.span {x}))))
  exact e1.toLinearEquiv.length_eq
end ReciprocityTheory.ChartRestriction.G.AI
