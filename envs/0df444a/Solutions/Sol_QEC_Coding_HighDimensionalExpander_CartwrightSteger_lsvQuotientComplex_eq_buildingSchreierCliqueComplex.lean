-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.lsvQuotientComplex_eq_buildingSchreierCliqueComplex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T03:59:48.079371+00:00
-- url     : https://prove2.me/submissions/93e4ac6d-d5d3-4f14-8fbb-16f1c5234e69

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_buildingSchreierGraph_eq_indexCayleyGraph

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    lsvQuotientComplex P r level =
      CayleyClique.schreierCliqueComplex
        (X := IndexFiniteGroup P r level)
        (buildingColoredGeneratorFinset P r :
          Set (BuildingCartwrightStegerLattice P r)) := by
  unfold lsvQuotientComplex CayleyClique.cayleyCliqueComplex
    CayleyClique.schreierCliqueComplex
  rw [buildingSchreierGraph_eq_indexCayleyGraph P r level]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
