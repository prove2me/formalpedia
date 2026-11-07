-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.sourceOnePlusY_map_eq_frobeniusProduct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:00:37.658122+00:00
-- url     : https://prove2.me/submissions/357d56b3-cf1d-4adf-b1b0-ae1a80f6d38c

import Mathlib.FieldTheory.Finite.Extension
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.PolynomialAlgebra
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_Arithmetic

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups RatFunc
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution (P : BasePrime) (r : Rank) :
    (sourceOnePlusY P r).map
        (algebraMap (BaseField P) (ConstantExtension P r)) =
      ∏ i ∈ Finset.range r.matrixRank,
        (1 + Polynomial.C
          ((constantFrobenius P r ^ i) (beta P r)) * Polynomial.X) := by
  simp [sourceOnePlusY, beta]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
