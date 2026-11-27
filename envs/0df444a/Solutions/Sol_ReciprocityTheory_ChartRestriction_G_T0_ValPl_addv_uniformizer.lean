-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.ValPl.addv_uniformizer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:28:20.527002+00:00
-- url     : https://prove2.me/submissions/e08895b0-29e5-40a8-8e00-da2ad37d19cf

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_algebraMap_OL_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_addv_count

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
include F
namespace ReciprocityTheory.ChartRestriction.G.T0.ValPl
theorem _root_.solution (v : HeightOneSpectrum (integralClosure O L)) {ϖ : O}
    (hϖ : Irreducible ϖ) :
    addv L v (algebraMap O L ϖ) = ((v.asIdeal.ramificationIdx O : ℕ) : WithTop ℤ) := by
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hinj : Function.Injective (algebraMap O (integralClosure O L)) := by
    intro a b hab
    first
    | exact algebraMap_OL_injective (F := F) (congrArg Subtype.val hab)
    | (apply algebraMap_OL_injective (F := F)
       rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L a,
         IsScalarTower.algebraMap_apply O (integralClosure O L) L b, hab])
  have hb : algebraMap O (integralClosure O L) ϖ ≠ 0 := by
    intro h
    apply hϖ0
    apply hinj
    rw [h, map_zero]
  rw [IsScalarTower.algebraMap_apply O (integralClosure O L) L ϖ, addv_count v _ hb]
  have hmax : maximalIdeal O = Ideal.span {ϖ} := by
    first
    | exact hϖ.maximalIdeal_eq
    | exact IsDiscreteValuationRing.Irreducible.maximalIdeal_eq hϖ
    | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hspan : Ideal.span {algebraMap O (integralClosure O L) ϖ} =
      (maximalIdeal O).map (algebraMap O (integralClosure O L)) := by
    rw [hmax, Ideal.map_span, Set.image_singleton]
  have hund : v.asIdeal.under O = maximalIdeal O := by
    haveI := v.isMaximal
    apply IsLocalRing.eq_maximalIdeal
    first
    | exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal v.asIdeal
    | exact Ideal.IsMaximal.under O v.asIdeal
    | infer_instance
  have hmap : Ideal.map (algebraMap O (integralClosure O L)) (v.asIdeal.under O) ≠ ⊥ := by
    rw [hund, ← hspan, Ne, Ideal.span_singleton_eq_bot]
    exact hb
  rw [hspan]
  norm_cast
  rw [← hund]
  first
  | (rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count, hmap, v.ne_bot]; done)
  | (rw [Ideal.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.ramificationIdx_eq_normalizedFactors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.ramificationIdx_eq_normalizedFactors_count, hmap, v.ne_bot]; done)
  | (rw [Ideal.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.ramificationIdx_eq_count_normalizedFactors, hmap, v.ne_bot]; done)
  | (rw [Ideal.IsDedekindDomain.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_count_normalizedFactors] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.IsDedekindDomain.ramificationIdx_eq_count_normalizedFactors, hmap, v.ne_bot]; done)
  | (rw [Ideal.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.count_normalizedFactors_eq_ramificationIdx, hmap, v.ne_bot]; done)
  | (rw [Ideal.IsDedekindDomain.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.IsDedekindDomain.count_normalizedFactors_eq_ramificationIdx] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.IsDedekindDomain.count_normalizedFactors_eq_ramificationIdx, hmap, v.ne_bot]; done)
  | (rw [Ideal.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.ramificationIdx_eq_factors_count, hmap, v.ne_bot]; done)
  | (rw [Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count] <;> first | exact hmap | exact v.isPrime | exact v.ne_bot | exact v.isMaximal | infer_instance | rfl) <;> done
  | (simp [Ideal.IsDedekindDomain.ramificationIdx_eq_factors_count, hmap, v.ne_bot]; done)
  | skip
  done
end ReciprocityTheory.ChartRestriction.G.T0.ValPl
