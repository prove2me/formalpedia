-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexRatioUnit_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:41:37.849575+00:00
-- url     : https://prove2.me/submissions/9ce0effd-cc53-4515-92c7-f884bf37253d

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexPlaceY_ne_zero
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
    indexRatioUnit P r level ≠ 1 := by
  intro h
  apply indexPlaceY_ne_zero P r level
  simp [indexPlaceY, IndexSelection.mobius, h]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
