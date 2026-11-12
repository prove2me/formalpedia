-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_indexColoredGeneratorFinset_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:38:50.859202+00:00
-- url     : https://prove2.me/submissions/15e9fdc2-4d77-41cc-9e05-04d8d0dbb021

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_indexColorGeneratorFinset_le

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    (indexColoredGeneratorFinset P r level).card ≤
      indexColoredGeneratorBound P r := by
  let colors := Finset.Icc 1 (r.matrixRank - 1)
  have hcolors : colors.card ≤ r.matrixRank := by
    cases r <;> decide +kernel
  calc
    (indexColoredGeneratorFinset P r level).card ≤
        colors.card * indexGeneratorBound P r ^ r.matrixRank := by
      exact Finset.card_biUnion_le_card_mul colors
        (indexColorGeneratorFinset P r level)
        (indexGeneratorBound P r ^ r.matrixRank)
        (fun k _ => card_indexColorGeneratorFinset_le P r level k)
    _ ≤ r.matrixRank * indexGeneratorBound P r ^ r.matrixRank :=
      Nat.mul_le_mul_right _ hcolors
    _ = indexColoredGeneratorBound P r := rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
