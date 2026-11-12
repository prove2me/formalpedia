-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvThreeDimensionalQuotient_tetrahedronFaces_unbounded_of_prasadStrongApproximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:12:47.302088+00:00
-- url     : https://prove2.me/submissions/411854d4-9adc-4100-a717-204f10399839

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_rankFour_vertices_le_four_mul_tetrahedronFaces
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerImage_unbounded_of_prasadStrongApproximation


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P .four))
    (bound : Nat) :
    ∃ level, bound < Fintype.card
      (SimplicialChain.Face (lsvThreeDimensionalQuotient P level) 4) := by
  obtain ⟨level, hlevel⟩ :=
    indexCartwrightStegerImage_unbounded_of_prasadStrongApproximation
      P .four hPrasad (4 * bound)
  have hvertices :
      4 * bound < Fintype.card (IndexFiniteGroup P .four level) := by
    rw [← Nat.card_eq_fintype_card]
    exact hlevel
  have hcover := card_rankFour_vertices_le_four_mul_tetrahedronFaces P level
  refine ⟨level, ?_⟩
  omega
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
