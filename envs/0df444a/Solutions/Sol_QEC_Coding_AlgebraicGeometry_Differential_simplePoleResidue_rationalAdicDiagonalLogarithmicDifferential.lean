-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_rationalAdicDiagonalLogarithmicDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:45:10.702804+00:00
-- url     : https://prove2.me/submissions/124ac10c-2b95-44df-8a3a-4f9c4c51095a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Trace_PolynomialMatrixDerivation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicDiagonalMatrixResidue
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_rationalAdicWeightedPolynomialLogDifferential


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
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicDiagonalLogarithmicDifferentialAtSimplePole p R a ha) =
      ∑ i, (GlobalPlace.rationalAdic p).residue
          (GlobalPlace.rationalAdicPolynomialToValuationRing p (R i i)) *
        (multiplicity p.asIdeal (Ideal.span ({a i} : Set k[X])) :
          (GlobalPlace.rationalAdic p).residueField) := by
  unfold rationalAdicDiagonalLogarithmicDifferentialAtSimplePole
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact simplePoleResidue_rationalAdicWeightedPolynomialLogDifferential
    p (R i i) (a i) (ha i)
end QEC.Coding.AlgebraicGeometry.Differential
