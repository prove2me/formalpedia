-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.HDiscVal.mem_integralClosure_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:49:26.033088+00:00
-- url     : https://prove2.me/submissions/eec226e8-0641-4235-b168-1d7c7fd73827

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HDiscAC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscVal_addv_eq_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscVal_addv_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_HDiscVal_addv_nonneg_iff

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
theorem _root_.solution (y : L) :
    y ∈ integralClosure O L ↔ ∀ w ∈ PlacesOver O L, 0 ≤ w y := by
  constructor
  · intro hy w hw
    obtain ⟨v, rfl⟩ := addv_eq_of_mem O F hw
    by_cases hy0 : y = 0
    · subst hy0
      rw [AddValuation.map_zero]
      exact le_top
    · rw [addv_nonneg_iff v hy0]
      first
        | exact v.valuation_le_one (⟨y, hy⟩ : integralClosure O L)
        | exact v.valuation_le_one L (⟨y, hy⟩ : integralClosure O L)
  · intro h
    by_cases hy0 : y = 0
    · subst hy0
      exact Subalgebra.zero_mem _
    · have hle : ∀ v : HeightOneSpectrum (integralClosure O L), v.valuation L y ≤ 1 :=
        fun v => (addv_nonneg_iff v hy0).1 (h _ (addv_mem O F v))
      have hr : y ∈ (algebraMap (integralClosure O L) L).range := by
        first
          | exact HeightOneSpectrum.mem_integers_of_valuation_le_one L y hle
          | exact HeightOneSpectrum.mem_integers_of_valuation_le_one y hle
      obtain ⟨b, hb⟩ := hr
      rw [← hb]
      exact b.2
end ReciprocityTheory.ChartRestriction.G.T0.HDiscVal
