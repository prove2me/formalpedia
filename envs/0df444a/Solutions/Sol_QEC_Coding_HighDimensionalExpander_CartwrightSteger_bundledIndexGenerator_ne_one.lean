-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.bundledIndexGenerator_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T17:41:43.313633+00:00
-- url     : https://prove2.me/submissions/15f045be-2b0e-4822-8dda-9593839f031b

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Order_Reduction
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_ApartmentCompletion
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingQuotient
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_CayleyClique
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Combinatorics_SimplicialChain
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_QuotientComplex
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_indexCartwrightStegerClassGenerator_ne_one


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Finset
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (u : ConstantProjectiveClass P r) :
    bundledIndexGenerator P r level u ≠ 1 := by
  intro hu
  apply indexCartwrightStegerClassGenerator_ne_one P r level u
  exact congrArg (fun g : IndexFiniteGroup P r level =>
    (g : PGL P r level)) hu
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
