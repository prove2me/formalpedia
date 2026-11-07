-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.residueXMinpoly_dvd_YMinpoly_comp_sourceY
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:01:32.451026+00:00
-- url     : https://prove2.me/submissions/15170ba8-0757-4d4c-a177-0efc0a2583ed

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
    residueXMinpoly P r level ∣
      (residueYMinpoly P r level).comp (sourceYPolynomial P r) := by
  apply minpoly.dvd (BaseField P) (residueAlpha P r level)
  rw [Polynomial.aeval_comp]
  have hy :
      Polynomial.aeval (residueAlpha P r level) (sourceYPolynomial P r) =
        residueGamma P r level := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]
    rfl
  rw [hy]
  exact minpoly.aeval (BaseField P) (residueGamma P r level)
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
