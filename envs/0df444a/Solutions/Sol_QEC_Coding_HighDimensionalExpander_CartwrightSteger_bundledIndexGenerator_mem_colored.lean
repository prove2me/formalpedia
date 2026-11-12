-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.bundledIndexGenerator_mem_colored
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:34:47.928385+00:00
-- url     : https://prove2.me/submissions/014b1fd3-1ffe-4b78-89f6-c8ce4a3b681f

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_bundledIndexGenerator_mem_colorOne

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    {u : Fin r.matrixRank → ConstantProjectiveClass P r}
    (hu : u ∈ buildingRelationTupleFinset P r) :
    bundledIndexGenerator P r level (u (rankZeroIndex r)) ∈
      indexColoredGeneratorFinset P r level := by
  have hcolor : 1 ∈ Finset.Icc 1 (r.matrixRank - 1) := by
    cases r <;> decide
  rw [indexColoredGeneratorFinset, Finset.mem_biUnion]
  exact ⟨1, hcolor, bundledIndexGenerator_mem_colorOne P r level hu⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
