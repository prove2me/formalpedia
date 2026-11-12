-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvTwoDimensionalQuotient_triangleFaces_unbounded_of_prasadStrongApproximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:04:25.362231+00:00
-- url     : https://prove2.me/submissions/377c9d96-80f7-49f1-9a71-71f0ef82aa43

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_rankThree_vertices_le_three_mul_triangleFaces
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerImage_unbounded_of_prasadStrongApproximation


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P .three))
    (bound : Nat) :
    ∃ level, bound < Fintype.card
      (SimplicialChain.Face (lsvTwoDimensionalQuotient P level) 3) := by
  obtain ⟨level, hlevel⟩ :=
    indexCartwrightStegerImage_unbounded_of_prasadStrongApproximation
      P .three hPrasad (3 * bound)
  have hvertices :
      3 * bound < Fintype.card (IndexFiniteGroup P .three level) := by
    rw [← Nat.card_eq_fintype_card]
    exact hlevel
  have hcover := card_rankThree_vertices_le_three_mul_triangleFaces P level
  refine ⟨level, ?_⟩
  omega
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
