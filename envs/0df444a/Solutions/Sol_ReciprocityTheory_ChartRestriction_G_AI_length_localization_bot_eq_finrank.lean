-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.length_localization_bot_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:27:59.81572+00:00
-- url     : https://prove2.me/submissions/b38b83b2-6e69-4488-bd4c-db228f62e0a0

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
theorem _root_.solution (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    length (Localization.AtPrime (⊥ : Ideal A)) (LocalizedModule (⊥ : Ideal A).primeCompl M) =
      (finrank A M : ℕ∞) := by
  have hfield : IsField (Localization.AtPrime (⊥ : Ideal A)) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot]
  letI : Field (Localization.AtPrime (⊥ : Ideal A)) := hfield.toField
  have hle : (⊥ : Ideal A).primeCompl ≤ nonZeroDivisors A := by
    intro a ha
    exact mem_nonZeroDivisors_of_ne_zero (fun h0 => ha (by rw [h0]; exact Submodule.zero_mem _))
  haveI : Module.Finite (Localization.AtPrime (⊥ : Ideal A)) (LocalizedModule (⊥ : Ideal A).primeCompl M) :=
    Module.Finite.of_isLocalizedModule (⊥ : Ideal A).primeCompl
      (LocalizedModule.mkLinearMap (⊥ : Ideal A).primeCompl M)
  rw [Module.length_of_free_of_finite, Module.length_eq_one, mul_one]
  rw [IsLocalization.finrank_eq (Localization.AtPrime (⊥ : Ideal A)) (⊥ : Ideal A).primeCompl hle,
    IsLocalizedModule.finrank_eq (⊥ : Ideal A).primeCompl
      (LocalizedModule.mkLinearMap (⊥ : Ideal A).primeCompl M) hle]
end ReciprocityTheory.ChartRestriction.G.AI
