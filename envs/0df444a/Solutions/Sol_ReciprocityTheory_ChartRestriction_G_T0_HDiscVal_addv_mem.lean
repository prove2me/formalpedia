-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HDiscVal.addv_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:36:05.118194+00:00
-- url     : https://prove2.me/submissions/76310590-00d2-4cdb-963d-79c00d3e1d01

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
open IsDedekindDomain WithZero ValPl
variable {O F L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field F]
  [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
  [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L]
  [IsDedekindDomain (integralClosure O L)] [IsFractionRing (integralClosure O L) L]
variable (O F)
include F
namespace ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
theorem _root_.solution (v : HeightOneSpectrum (integralClosure O L)) : addv L v ∈ PlacesOver O L := by
  have hval : ∀ y : L, y ≠ 0 →
      addv L v y = ((-WithZero.log (v.valuation L y) : ℤ) : WithTop ℤ) := by
    intro y hy
    unfold addv
    rw [AddValuation.of_apply, if_neg hy]
  have hP : v.asIdeal.comap (algebraMap O (integralClosure O L)) = IsLocalRing.maximalIdeal O := by
    haveI := v.isMaximal
    apply IsLocalRing.eq_maximalIdeal
    first
      | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
      | exact Ideal.IsMaximal.under O v.asIdeal
      | infer_instance
  simp only [PlacesOver, IsNormDiscrete, Set.mem_setOf_eq]
  refine ⟨⟨fun a ha => ?_, ?_⟩, fun x => ?_⟩
  · rw [hval a ha]
    exact WithTop.coe_ne_top
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer L
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact absurd hπ.symm (by simp)
    refine ⟨π, ?_⟩
    rw [hval π hπ0, hπ]
    first
      | simp
      | rfl
  · have hx : algebraMap O L x =
        algebraMap (integralClosure O L) L (algebraMap O (integralClosure O L) x) :=
      IsScalarTower.algebraMap_apply O (integralClosure O L) L x
    by_cases hx0 : algebraMap O L x = 0
    · have hx00 : x = 0 := by
        have h1 : algebraMap O F x = 0 := by
          apply (algebraMap F L).injective
          rw [← IsScalarTower.algebraMap_apply, map_zero]
          exact hx0
        exact IsFractionRing.injective O F (by rw [h1, map_zero])
      subst hx00
      simp
    · rw [hval _ hx0]
      have hv : v.valuation L (algebraMap O L x) ≠ 0 := by simpa using hx0
      have hle := WithZero.log_le_log hv one_ne_zero
      have hge := WithZero.log_le_log one_ne_zero hv
      rw [WithZero.log_one] at hle hge
      have hmem : v.valuation L (algebraMap O L x) < 1 ↔
          algebraMap O (integralClosure O L) x ∈ v.asIdeal := by
        rw [hx]
        first
          | exact v.valuation_lt_one_iff_mem _
          | exact v.valuation_lt_one_iff_mem L _
      have hint : v.valuation L (algebraMap O L x) ≤ 1 := by
        rw [hx]
        first
          | exact v.valuation_le_one _
          | exact v.valuation_le_one L _
      rw [← hP, Ideal.mem_comap, ← hmem]
      constructor
      · have h3 := hle.2 hint
        exact_mod_cast (show (0 : ℤ) ≤ -WithZero.log (v.valuation L (algebraMap O L x)) by omega)
      · constructor
        · intro h
          have h' : (0 : ℤ) < -WithZero.log (v.valuation L (algebraMap O L x)) := by
            exact_mod_cast h
          refine lt_of_le_of_ne hint (fun he => ?_)
          rw [he, WithZero.log_one] at h'
          omega
        · intro h
          have h1 : ¬ (0 ≤ WithZero.log (v.valuation L (algebraMap O L x))) :=
            fun h0 => (not_le.2 h) (hge.1 h0)
          have h2 : (0 : ℤ) < -WithZero.log (v.valuation L (algebraMap O L x)) := by omega
          exact_mod_cast h2
end ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
