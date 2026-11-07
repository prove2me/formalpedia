-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXMinpoly_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:31.069957+00:00
-- url     : https://prove2.me/submissions/ba98866c-6039-4ff6-84e2-79f4f36984dc

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
theorem _root_.solution (P : BasePrime) (r : Rank) (level : Nat) :
    Irreducible (residueXMinpoly P r level) :=
  minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
