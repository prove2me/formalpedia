-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValPl.addv_mem_placesOver
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:35:57.71177+00:00
-- url     : https://prove2.me/submissions/db143bbb-94f2-4fae-b045-20e110b82032

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_addv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_addv_nonneg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_addv_pos_iff

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
namespace ReciprocityTheory.ChartRestriction.G.T0.ValPl
theorem _root_.solution (v : HeightOneSpectrum (integralClosure O L)) :
    addv L v ∈ PlacesOver O L := by
  rw [PlacesOver, Set.mem_setOf_eq, IsNormDiscrete]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro a ha
    rw [addv_apply v ha]
    exact WithTop.coe_ne_top
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer L
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at hπ
      exact absurd hπ.symm (by simp)
    refine ⟨π, ?_⟩
    rw [addv_apply v hπ0, hπ, log_exp]
    simp
  · intro x
    haveI := v.isMaximal
    have hcomap : v.asIdeal.comap (algebraMap O (integralClosure O L)) = maximalIdeal O := by
      apply IsLocalRing.eq_maximalIdeal
      first
      | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
      | exact Ideal.IsMaximal.under O v.asIdeal
      | infer_instance
    rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L x, ← hcomap, Ideal.mem_comap]
    exact ⟨addv_nonneg v _, addv_pos_iff v _⟩
end ReciprocityTheory.ChartRestriction.G.T0.ValPl
