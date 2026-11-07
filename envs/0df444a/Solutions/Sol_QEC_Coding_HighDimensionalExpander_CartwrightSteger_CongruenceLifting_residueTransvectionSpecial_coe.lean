-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting.residueTransvectionSpecial_coe
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:40:55.853763+00:00
-- url     : https://prove2.me/submissions/32ddef9f-afe5-4dda-b75a-75cc45a23346

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSelection
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_Congruence

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups
open QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
open Matrix
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat)
    (c : ResidueField P r level) :
    (residueTransvectionSpecial P r level c :
        Matrix (Fin r.matrixRank) (Fin r.matrixRank)
          (ResidueField P r level)) =
      Matrix.transvection (rankFirstIndex r) (rankSecondIndex r) c :=
  rfl
end QEC.Coding.HighDimensionalExpander.CartwrightSteger.CongruenceLifting
