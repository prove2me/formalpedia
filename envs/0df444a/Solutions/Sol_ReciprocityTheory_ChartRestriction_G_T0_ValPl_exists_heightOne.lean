-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValPl.exists_heightOne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:29:47.744487+00:00
-- url     : https://prove2.me/submissions/34e16619-83bf-415a-852b-78118b069ba3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_algebraMap_OL_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValPl
open IsDedekindDomain WithZero IsLocalRing
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
variable (O F L)
include F
namespace ReciprocityTheory.ChartRestriction.G.T0.ValPl
theorem _root_.solution (Q : Ideal (integralClosure O L)) (hQ : Q.IsMaximal) :
    ∃ v : HeightOneSpectrum (integralClosure O L), v.asIdeal = Q := by
  have hinj : Function.Injective (algebraMap O (integralClosure O L)) := by
    intro a b hab
    first
    | exact algebraMap_OL_injective (F := F) (congrArg Subtype.val hab)
    | (apply algebraMap_OL_injective (F := F)
       rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L a,
         IsScalarTower.algebraMap_apply O (integralClosure O L) L b, hab])
  have hne : Q ≠ ⊥ := by
    rintro rfl
    have hB : IsField (integralClosure O L) := Ring.isField_iff_maximal_bot.mpr hQ
    have hO : IsField O := isField_of_isIntegral_of_isField hinj hB
    have hmax : (⊥ : Ideal O).IsMaximal := Ring.isField_iff_maximal_bot.mp hO
    exact absurd (IsLocalRing.eq_maximalIdeal hmax).symm IsDiscreteValuationRing.not_a_field'
  exact ⟨⟨Q, hQ.isPrime, hne⟩, rfl⟩
end ReciprocityTheory.ChartRestriction.G.T0.ValPl
