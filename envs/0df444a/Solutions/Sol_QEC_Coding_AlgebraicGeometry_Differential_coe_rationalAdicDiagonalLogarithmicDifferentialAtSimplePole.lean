-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicDiagonalLogarithmicDifferentialAtSimplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:43:26.816218+00:00
-- url     : https://prove2.me/submissions/0b8aacfb-bca5-48ff-b185-79f7f1fa2e35

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicDiagonalMatrixResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_trace_map_mul_rationalDiagonalInverse_derivative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicWeightedPolynomialLogDifferentialAtSimplePole


set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
variable {k : Type*} [Field k]
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : IsDedekindDomain.HeightOneSpectrum k[X])
    (R : Matrix n n k[X]) (a : n → k[X])
    (ha : ∀ i, a i ≠ 0) :
    ((rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p R a ha :
      simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      Matrix.trace
          (((algebraMap k[X] (RatFunc k)).mapMatrix R *
              rationalDiagonalMatrixInverse a) *
            entrywiseMatrixDerivation
              (RatFuncDerivation.rationalDerivation
                (k := k) (M := RatFunc k) 1)
              ((algebraMap k[X] (RatFunc k)).mapMatrix
                (Matrix.diagonal a))) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  unfold rationalAdicDiagonalLogarithmicDifferentialAtSimplePole
  change
    (simplePoleDifferentialLattice (GlobalPlace.rationalAdic p)).subtype
      (∑ i, rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
        p (R i i) (a i) (ha i)) = _
  rw [map_sum]
  calc
    (∑ i, (simplePoleDifferentialLattice
        (GlobalPlace.rationalAdic p)).subtype
          (rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
            p (R i i) (a i) (ha i))) =
        ∑ i, (algebraMap k[X] (RatFunc k) (R i i) *
            (algebraMap k[X] (RatFunc k) (a i))⁻¹ *
            algebraMap k[X] (RatFunc k) (a i).derivative) •
          functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
      apply Finset.sum_congr rfl
      intro i _
      exact coe_rationalAdicWeightedPolynomialLogDifferentialAtSimplePole
        p (R i i) (a i) (ha i)
    _ = (∑ i, algebraMap k[X] (RatFunc k) (R i i) *
          (algebraMap k[X] (RatFunc k) (a i))⁻¹ *
          algebraMap k[X] (RatFunc k) (a i).derivative) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
      rw [Finset.sum_smul]
    _ = _ := by
      rw [trace_map_mul_rationalDiagonalInverse_derivative]
end QEC.Coding.AlgebraicGeometry.Differential
