-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvQuotientComplex_vertexFaces_unbounded_of_prasadStrongApproximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:43:25.434846+00:00
-- url     : https://prove2.me/submissions/04360db5-977b-4ac5-aa20-221750811c80

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_card_lsvQuotientComplex_vertexFaces
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerImage_unbounded_of_prasadStrongApproximation


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (hPrasad : DenseRange
      (cyclicAlgebraNormOneToArithmeticFiniteAdeleNormOne P r))
    (bound : Nat) :
    ∃ level, bound < Fintype.card
      (SimplicialChain.Face (lsvQuotientComplex P r level) 1) := by
  obtain ⟨level, hlevel⟩ :=
    indexCartwrightStegerImage_unbounded_of_prasadStrongApproximation
      P r hPrasad bound
  refine ⟨level, ?_⟩
  rw [card_lsvQuotientComplex_vertexFaces]
  rw [← Nat.card_eq_fintype_card]
  exact hlevel
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
