-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.range_globalIntegralUnitPGLHom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:38:30.573871+00:00
-- url     : https://prove2.me/submissions/f775831e-0e76-4c72-9d99-2318fc824332

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_SkewRepresentation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Integral_ProjectiveUnits
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitGLHom_coe
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_eq_constant_mul_zpow
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_globalIntegralUnitPGLHom_monomial
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_constantUnitMatrix_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_mem_skewLaurentIntSupport
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentMonomialUnit_val
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_skewLaurentToGlobalMatrix_single
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.constantUnitMatrix_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_skewLaurentIntSupport
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentMonomialUnit_val
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.skewLaurentToGlobalMatrix_single


attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitGLHom_coe
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.globalIntegralUnitPGLHom_monomial

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) :
    (globalIntegralUnitPGLHom P r).range =
      GlobalIntegralCompactCyclicSubgroup P r := by
  apply le_antisymm
  · rintro g ⟨u, rfl⟩
    obtain ⟨c, n, hu⟩ :=
      globalIntegralUnitPGLHom_eq_constant_mul_zpow P r u
    rw [hu]
    exact (GlobalIntegralCompactCyclicSubgroup P r).mul_mem
      (Subgroup.subset_closure
        (Set.mem_union_left _ (Set.mem_range_self c)))
      ((GlobalIntegralCompactCyclicSubgroup P r).zpow_mem
        (Subgroup.subset_closure
          (Set.mem_union_right _ (Set.mem_singleton _))) n)
  · rw [GlobalIntegralCompactCyclicSubgroup]
    apply (Subgroup.closure_le _).mpr
    rintro g (hg | hg)
    · obtain ⟨c, rfl⟩ := hg
      refine ⟨skewLaurentMonomialUnit P r c 0, ?_⟩
      simp
    · rw [Set.mem_singleton_iff] at hg
      subst g
      refine ⟨skewLaurentMonomialUnit P r 1 1, ?_⟩
      simp [globalConstantPGLHom]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
