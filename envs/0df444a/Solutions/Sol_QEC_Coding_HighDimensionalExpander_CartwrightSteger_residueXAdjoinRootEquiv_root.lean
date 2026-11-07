-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXAdjoinRootEquiv_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:31:46.63089+00:00
-- url     : https://prove2.me/submissions/82a231d0-f682-40dc-9bf0-a715e5598e1e

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
    residueXAdjoinRootEquiv P r level
      (AdjoinRoot.root (residueXMinpoly P r level)) =
        residueAlpha P r level := by
  unfold residueXAdjoinRootEquiv
  change (IsAdjoinRootMonic.mkOfAdjoinEqTop'
    (residueX_algebraAdjoin_eq_top P r level)).root = residueAlpha P r level
  exact IsAdjoinRootMonic.mkOfAdjoinEqTop'_root
    (residueX_algebraAdjoin_eq_top P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
