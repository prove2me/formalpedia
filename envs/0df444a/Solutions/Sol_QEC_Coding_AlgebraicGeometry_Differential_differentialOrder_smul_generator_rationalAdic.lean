-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_smul_generator_rationalAdic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:46:29.824515+00:00
-- url     : https://prove2.me/submissions/7f3c3cec-9b61-4ee4-934a-8b98c9d078e3

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_generator_rationalAdic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_smul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero


set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) (f : RatFunc k) (hf : f ≠ 0) :
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (smul_ne_zero hf
          (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))) =
      (GlobalPlace.rationalAdic p).order f := by
  calc
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p)
        (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (smul_ne_zero hf
          (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))) =
        (GlobalPlace.rationalAdic p).order f +
          differentialOrder (k := k) (F := RatFunc k)
            (GlobalPlace.rationalAdic p)
            (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
            (functionFieldDifferentialGenerator_ne_zero
              (k := k) (F := RatFunc k)) :=
      differentialOrder_smul (k := k) (F := RatFunc k)
        (GlobalPlace.rationalAdic p) f hf
        (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))
    _ = (GlobalPlace.rationalAdic p).order f := by
      rw [differentialOrder_generator_rationalAdic, add_zero]
end QEC.Coding.AlgebraicGeometry.Differential
