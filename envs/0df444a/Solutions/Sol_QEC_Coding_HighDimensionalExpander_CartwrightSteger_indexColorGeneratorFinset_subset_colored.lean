-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.indexColorGeneratorFinset_subset_colored
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:55:07.616762+00:00
-- url     : https://prove2.me/submissions/9a819bcd-8cf2-416a-8483-1b537490fc40

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
    (hk : k ∈ Finset.Icc 1 (r.matrixRank - 1)) :
    indexColorGeneratorFinset P r level k ⊆
      indexColoredGeneratorFinset P r level := by
  intro g hg
  rw [indexColoredGeneratorFinset, Finset.mem_biUnion]
  exact ⟨k, hk, hg⟩
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
