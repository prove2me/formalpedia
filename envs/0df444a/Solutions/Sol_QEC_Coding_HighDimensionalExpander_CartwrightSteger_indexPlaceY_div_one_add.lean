-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexPlaceY_div_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:42:27.172193+00:00
-- url     : https://prove2.me/submissions/813aad69-a910-46b0-b877-c17f8e1837b3

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexRatioUnit_ne_one
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueXAdjoinRootEquiv_root
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_residueYAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
attribute [local simp] QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open IntermediateField
open IndexSelection
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    indexPlaceY P r level / (1 + indexPlaceY P r level) =
      (indexRatioUnit P r level : ResidueField P r level) := by
  have hu : (indexRatioUnit P r level : ResidueField P r level) ≠ 1 := by
    intro h
    apply indexRatioUnit_ne_one P r level
    apply Units.ext
    simpa using h
  have hden :
      1 - (indexRatioUnit P r level : ResidueField P r level) ≠ 0 :=
    sub_ne_zero.mpr hu.symm
  rw [indexPlaceY, IndexSelection.mobius]
  have hone :
      1 + (indexRatioUnit P r level : ResidueField P r level) /
          (1 - (indexRatioUnit P r level : ResidueField P r level)) =
        (1 - (indexRatioUnit P r level : ResidueField P r level))⁻¹ := by
    field_simp [hden]
    ring
  rw [hone, div_inv_eq_mul]
  field_simp [hden]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
