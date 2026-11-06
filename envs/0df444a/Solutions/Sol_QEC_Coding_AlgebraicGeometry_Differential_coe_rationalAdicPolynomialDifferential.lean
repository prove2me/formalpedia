-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:33:27.500203+00:00
-- url     : https://prove2.me/submissions/e85767aa-6d14-4e88-af28-8d0460061d02

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Local_Residue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing



set_option autoImplicit false
open scoped Polynomial RatFunc
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (b : k[X]) :
    ((rationalAdicPolynomialDifferential p b :
      localDifferentialLattice (GlobalPlace.rationalAdic p)) :
        Differential k (RatFunc k)) =
      algebraMap k[X] (RatFunc k) b •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) := by
  change
    ((GlobalPlace.rationalAdicPolynomialToValuationRing p b :
      (GlobalPlace.rationalAdic p).valuationRing) : RatFunc k) •
        functionFieldDifferentialGenerator (k := k) (F := RatFunc k) = _
  rw [GlobalPlace.coe_rationalAdicPolynomialToValuationRing]
end QEC.Coding.AlgebraicGeometry.Differential
