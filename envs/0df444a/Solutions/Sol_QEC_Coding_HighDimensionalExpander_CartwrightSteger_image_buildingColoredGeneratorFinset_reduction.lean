-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.image_buildingColoredGeneratorFinset_reduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:27:33.417081+00:00
-- url     : https://prove2.me/submissions/f595b8f2-c47f-407e-a0ae-2e8126338c5c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_image_buildingColorGeneratorFinset_reduction

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    (buildingColoredGeneratorFinset P r).image
        (buildingLatticeFiniteReduction P r level) =
      indexColoredGeneratorFinset P r level := by
  classical
  rw [buildingColoredGeneratorFinset, indexColoredGeneratorFinset,
    Finset.biUnion_image]
  apply Finset.biUnion_congr rfl
  intro k hk
  exact image_buildingColorGeneratorFinset_reduction P r level k
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
