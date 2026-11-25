-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValPl.norm_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:47:31.326554+00:00
-- url     : https://prove2.me/submissions/86d61f53-9231-4b7c-b85f-3cf6b9c02784

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValPlRes
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValNorm
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_normOrd


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
open IsDedekindDomain IsLocalRing
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
include F
namespace ReciprocityTheory.ChartRestriction.G.T0.ValPl
theorem _root_.solution (b : integralClosure O L) (hb : b ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ u : O, IsUnit u ∧
      Algebra.norm F (algebraMap (integralClosure O L) L b) = algebraMap O F
        (ϖ ^ (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O *
          Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})))
          * u) := by
  haveI : Module.Finite O (integralClosure O L) :=
    IsIntegralClosure.finite O F L (integralClosure O L)
  have hinj : Function.Injective (algebraMap O L) := by
    rw [IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  have hinjB : Function.Injective (algebraMap O (integralClosure O L)) := by
    intro x y hxy
    apply hinj
    rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L x,
      IsScalarTower.algebraMap_apply O (integralClosure O L) L y, hxy]
  haveI : NoZeroSMulDivisors O (integralClosure O L) := by
    refine ⟨fun {c x} h => ?_⟩
    rw [Algebra.smul_def, mul_eq_zero] at h
    exact h.imp_left (fun h' => hinjB (h'.trans (map_zero _).symm))
  have hN := ReciprocityTheory.MultiplicativeHeights.Closed.normOrd O (integralClosure O L) b hb
  have hne : Algebra.norm O b ≠ 0 := by
    intro h0
    rw [h0, IsDiscreteValuationRing.addVal_zero] at hN
    exact ENat.top_ne_coe _ hN
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  have hn := IsDiscreteValuationRing.addVal_def _ u hϖ n hu
  rw [hn] at hN
  have hnN : n = ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal}, Q.1.inertiaDeg O *
      Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})) := by
    exact_mod_cast hN
  have hsum : (∑ᶠ v : HeightOneSpectrum (integralClosure O L), v.asIdeal.inertiaDeg O *
      Multiset.count v.asIdeal (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b}))) = n := by
    rw [hnN]
    exact finsum_comp_equiv (hoEquiv O F L)
      (f := fun Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal} => Q.1.inertiaDeg O *
        Multiset.count Q.1 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {b})))
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure O L) (nonZeroDivisors O)) L :=
    IsIntegralClosure.isLocalization O F L (integralClosure O L)
  refine ⟨u, u.isUnit, ?_⟩
  rw [Algebra.norm_localization O (nonZeroDivisors O) b, hu, hsum, mul_comm (u : O)]
end ReciprocityTheory.ChartRestriction.G.T0.ValPl
