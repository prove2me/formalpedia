-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.betaLinearPolynomial_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:00:31.76607+00:00
-- url     : https://prove2.me/submissions/ea03c15a-8755-43e6-8579-4ee06ade85be

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
    betaLinearPolynomial P r =
      (1 + Polynomial.X : PolynomialRing P).map
        (algebraMap (BaseField P) (ConstantExtension P r)) := by
  simp [betaLinearPolynomial, beta]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
