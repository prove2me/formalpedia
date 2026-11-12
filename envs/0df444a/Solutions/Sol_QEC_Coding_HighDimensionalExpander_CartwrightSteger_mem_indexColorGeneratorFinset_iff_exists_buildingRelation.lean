-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.mem_indexColorGeneratorFinset_iff_exists_buildingRelation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:59:18.764136+00:00
-- url     : https://prove2.me/submissions/d19f070a-6ff3-4af2-ba42-70ac74a6b330

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
    (P : BasePrime) (r : Rank) (level k : Nat)
    (g : IndexFiniteGroup P r level) :
    g ∈ indexColorGeneratorFinset P r level k ↔
      ∃ u ∈ buildingRelationTupleFinset P r,
        indexGeneratorPrefixProduct P r level k u = g := by
  classical
  rw [indexColorGeneratorFinset, Finset.mem_image]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
