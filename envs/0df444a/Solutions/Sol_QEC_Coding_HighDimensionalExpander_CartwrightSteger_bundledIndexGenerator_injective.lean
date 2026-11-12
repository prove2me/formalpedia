-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.bundledIndexGenerator_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:16:32.93067+00:00
-- url     : https://prove2.me/submissions/c21a9e5c-87e0-4a53-9508-84e2fe4cb852

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerClassGenerator_injective


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    Function.Injective (bundledIndexGenerator P r level) := by
  intro u v huv
  apply indexCartwrightStegerClassGenerator_injective P r level
  exact congrArg (fun g : IndexFiniteGroup P r level =>
    (g : PGL P r level)) huv
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
