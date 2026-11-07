-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.buildingCompactNormalForm_conj_constantCyclicMonomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:03:15.035644+00:00
-- url     : https://prove2.me/submissions/bcada432-eca5-4802-a1e4-ae00cc338b69

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingCyclicGeneratorPGL_pow_conj_constant

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (u v : (ConstantExtension P r)ˣ)
    (j k : ℕ) :
    (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ j) *
        (buildingConstantPGLHom P r v *
          buildingCyclicGeneratorPGL P r ^ k) *
        (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ j)⁻¹ =
      buildingConstantPGLHom P r
          (compactConjugationDiagonalUnit P r u v j k) *
        buildingCyclicGeneratorPGL P r ^ k := by
  have hv := buildingCyclicGeneratorPGL_pow_conj_constant P r j v
  have huInv := buildingCyclicGeneratorPGL_pow_conj_constant P r k u⁻¹
  calc
    (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ j) *
        (buildingConstantPGLHom P r v *
          buildingCyclicGeneratorPGL P r ^ k) *
        (buildingConstantPGLHom P r u *
          buildingCyclicGeneratorPGL P r ^ j)⁻¹ =
      buildingConstantPGLHom P r u *
        (buildingCyclicGeneratorPGL P r ^ j *
          buildingConstantPGLHom P r v *
          (buildingCyclicGeneratorPGL P r ^ j)⁻¹) *
        buildingCyclicGeneratorPGL P r ^ k *
        (buildingConstantPGLHom P r u)⁻¹ := by group
    _ = buildingConstantPGLHom P r u *
        buildingConstantPGLHom P r
          ((constantFrobeniusUnitEquiv P r ^ j) v) *
        buildingCyclicGeneratorPGL P r ^ k *
        (buildingConstantPGLHom P r u)⁻¹ := by rw [hv]
    _ = buildingConstantPGLHom P r u *
        buildingConstantPGLHom P r
          ((constantFrobeniusUnitEquiv P r ^ j) v) *
        (buildingCyclicGeneratorPGL P r ^ k *
          (buildingConstantPGLHom P r u)⁻¹ *
          (buildingCyclicGeneratorPGL P r ^ k)⁻¹) *
        buildingCyclicGeneratorPGL P r ^ k := by group
    _ = buildingConstantPGLHom P r u *
        buildingConstantPGLHom P r
          ((constantFrobeniusUnitEquiv P r ^ j) v) *
        buildingConstantPGLHom P r
          ((constantFrobeniusUnitEquiv P r ^ k) u⁻¹) *
        buildingCyclicGeneratorPGL P r ^ k := by
          rw [← map_inv, huInv]
    _ = buildingConstantPGLHom P r
          (compactConjugationDiagonalUnit P r u v j k) *
        buildingCyclicGeneratorPGL P r ^ k := by
          rw [compactConjugationDiagonalUnit, map_mul, map_mul, map_inv]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
