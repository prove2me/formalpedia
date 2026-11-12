-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.card_rankThree_vertices_le_three_mul_triangleFaces
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:42:50.805194+00:00
-- url     : https://prove2.me/submissions/17b42216-6058-4d03-9373-963223405054

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_exists_triangleFace_containing_vertex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_vertices_le_faceSize_mul_card_faces

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (level : Nat) :
    Fintype.card (IndexFiniteGroup P .three level) ≤
      3 * Fintype.card
        (SimplicialChain.Face (lsvTwoDimensionalQuotient P level) 3) := by
  exact card_vertices_le_faceSize_mul_card_faces 3
    (exists_triangleFace_containing_vertex P level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
