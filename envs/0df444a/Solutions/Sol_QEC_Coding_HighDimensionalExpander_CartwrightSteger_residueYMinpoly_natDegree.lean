-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueYMinpoly_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T12:31:48.627202+00:00
-- url     : https://prove2.me/submissions/d22d98c1-835d-4c15-bd22-5954d54ede49

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic
import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.IsAdjoinRoot
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_ResidueSelection
import Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Rank_residueExponent_ne_zero


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open Polynomial IntermediateField
open ResidueSelection
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) (level : Nat) :
    (residueYMinpoly P r level).natDegree = r.residueExponent level := by
  calc
    (residueYMinpoly P r level).natDegree =
        Module.finrank (BaseField P) (ResidueField P r level) := by
      apply (Field.primitive_element_iff_minpoly_natDegree_eq
        (BaseField P) (residueGamma P r level)).mp
      exact residueGamma_adjoin_eq_top P r level
    _ = r.residueExponent level :=
      GaloisField.finrank P.q (Rank.residueExponent_ne_zero r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
