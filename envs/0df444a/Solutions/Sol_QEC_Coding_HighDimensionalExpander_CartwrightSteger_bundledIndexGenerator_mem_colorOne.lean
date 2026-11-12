-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.bundledIndexGenerator_mem_colorOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:27:30.0502+00:00
-- url     : https://prove2.me/submissions/19456edc-4b03-43fe-ab1c-38675741d5e6

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    {u : Fin r.matrixRank → ConstantProjectiveClass P r}
    (hu : u ∈ buildingRelationTupleFinset P r) :
    bundledIndexGenerator P r level (u (rankZeroIndex r)) ∈
      indexColorGeneratorFinset P r level 1 := by
  rw [indexColorGeneratorFinset]
  exact Finset.mem_image.mpr
    ⟨u, hu, indexGeneratorPrefixProduct_one P r level u⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
