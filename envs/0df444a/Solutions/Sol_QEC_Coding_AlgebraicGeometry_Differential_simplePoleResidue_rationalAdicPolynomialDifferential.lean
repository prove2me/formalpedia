-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.simplePoleResidue_rationalAdicPolynomialDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:34:24.800654+00:00
-- url     : https://prove2.me/submissions/273acd14-36b8-48f3-8254-718f06517b5a

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_simplePoleResidue_eq_zero_of_mem_localDifferentialLattice


set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    simplePoleResidue (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (rationalAdicPolynomialDifferentialAtSimplePole p b) = 0 := by
  exact simplePoleResidue_eq_zero_of_mem_localDifferentialLattice
    (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
    (rationalAdicPolynomialDifferentialAtSimplePole p b)
    (rationalAdicPolynomialDifferential p b).property
end QEC.Coding.AlgebraicGeometry.Differential
