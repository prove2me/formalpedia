-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankThree_triangle_face_incidence_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:03:01.189758+00:00
-- url     : https://prove2.me/submissions/1c79fe82-4488-4acb-8acc-0d2acc416d42

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_cayley_face_incidence_formula

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (level : Nat) :
    3 * Fintype.card
        (SimplicialChain.Face (lsvTwoDimensionalQuotient P level) 3) =
      Fintype.card (IndexFiniteGroup P .three level) *
        Fintype.card
          {σ : SimplicialChain.Face
              (lsvTwoDimensionalQuotient P level) 3 //
            1 ∈ σ.vertices} := by
  exact cayley_face_incidence_formula
    (indexColoredGeneratorFinset P .three level :
      Set (IndexFiniteGroup P .three level)) 3
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
