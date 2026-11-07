-- Prove2me | solution 1 for QEC.Coding.HypergraphProduct.extendedAlgebraicCSSMinimumDistance_eq_inputDistanceMinimum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T04:47:18.042828+00:00
-- url     : https://prove2.me/submissions/f4374472-4df6-4e00-9329-8e0fd3e72fdf

import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_UpperBound
import Definitions.Def_QEC_Coding_HypergraphProduct_Distance_Formula
import Theorems.Thm_QEC_Coding_HypergraphProduct_extendedAlgebraicCSSMinimumDistance_le_firstTranspose_of_secondTranspose_ne_top
import Theorems.Thm_QEC_Coding_HypergraphProduct_extendedAlgebraicCSSMinimumDistance_le_first_of_second_ne_top
import Theorems.Thm_QEC_Coding_HypergraphProduct_extendedAlgebraicCSSMinimumDistance_le_secondTranspose_of_firstTranspose_ne_top
import Theorems.Thm_QEC_Coding_HypergraphProduct_extendedAlgebraicCSSMinimumDistance_le_second_of_first_ne_top
import Theorems.Thm_QEC_Coding_HypergraphProduct_inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.HypergraphProduct
universe u
namespace QEC.Coding.HypergraphProduct
theorem _root_.solution
    {rowOne colOne rowTwo colTwo : Type u}
    [Fintype rowOne] [DecidableEq rowOne]
    [Fintype colOne] [DecidableEq colOne]
    [Fintype rowTwo] [DecidableEq rowTwo]
    [Fintype colTwo] [DecidableEq colTwo]
    (D : Data (ZMod 2) rowOne colOne rowTwo colTwo)
    (hEquality : DistanceEqualityCondition D) :
    extendedAlgebraicCSSMinimumDistance
        (binaryCSSCode D).xCode (binaryCSSCode D).zCode =
      inputDistanceMinimum D := by
  apply le_antisymm
  · rcases hEquality with hFirst | hSecond | hFirstTranspose | hSecondTranspose
    · exact (extendedAlgebraicCSSMinimumDistance_le_first_of_second_ne_top
        D hFirst.2).trans_eq hFirst.1
    · exact (extendedAlgebraicCSSMinimumDistance_le_second_of_first_ne_top
        D hSecond.2).trans_eq hSecond.1
    · exact
        (extendedAlgebraicCSSMinimumDistance_le_firstTranspose_of_secondTranspose_ne_top
          D hFirstTranspose.2).trans_eq hFirstTranspose.1
    · exact
        (extendedAlgebraicCSSMinimumDistance_le_secondTranspose_of_firstTranspose_ne_top
          D hSecondTranspose.2).trans_eq hSecondTranspose.1
  · exact inputDistanceMinimum_le_extendedAlgebraicCSSMinimumDistance D
end QEC.Coding.HypergraphProduct
