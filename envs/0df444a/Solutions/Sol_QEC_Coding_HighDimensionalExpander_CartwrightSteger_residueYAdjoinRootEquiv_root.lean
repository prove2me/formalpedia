-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYAdjoinRootEquiv_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:31:45.567315+00:00
-- url     : https://prove2.me/submissions/9819470d-5adb-4962-94ca-bbe7d1c0b62c

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.IsAdjoinRoot
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Polynomial IntermediateField
open ResidueSelection
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank) (level : Nat) :
    residueYAdjoinRootEquiv P r level
      (AdjoinRoot.root (residueYMinpoly P r level)) =
        residueGamma P r level := by
  unfold residueYAdjoinRootEquiv
  change (IsAdjoinRootMonic.mkOfAdjoinEqTop'
    (residueY_algebraAdjoin_eq_top P r level)).root = residueGamma P r level
  exact IsAdjoinRootMonic.mkOfAdjoinEqTop'_root
    (residueY_algebraAdjoin_eq_top P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
