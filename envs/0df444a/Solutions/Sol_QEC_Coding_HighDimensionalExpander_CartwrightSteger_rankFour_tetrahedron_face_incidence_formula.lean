-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.rankFour_tetrahedron_face_incidence_formula
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:03:16.157585+00:00
-- url     : https://prove2.me/submissions/bd20a267-ab67-4a18-ab05-f4fd50dd12b5

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
    4 * Fintype.card
        (SimplicialChain.Face (lsvThreeDimensionalQuotient P level) 4) =
      Fintype.card (IndexFiniteGroup P .four level) *
        Fintype.card
          {σ : SimplicialChain.Face
              (lsvThreeDimensionalQuotient P level) 4 //
            1 ∈ σ.vertices} := by
  exact cayley_face_incidence_formula
    (indexColoredGeneratorFinset P .four level :
      Set (IndexFiniteGroup P .four level)) 4
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
