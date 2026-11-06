-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.differentialOrder_smul_generator_rationalInfinity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:48:04.227378+00:00
-- url     : https://prove2.me/submissions/256d2f3d-ee13-4f61-8c63-8434f74ff81b

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicSimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_InfinitySimpleFractionResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_generator_rationalInfinity
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
    (f : RatFunc k) (hf : f ≠ 0) :
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (smul_ne_zero hf
          (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))) =
      (GlobalPlace.rationalInfinity k).order f - 2 := by
  calc
    differentialOrder (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k)
        (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (smul_ne_zero hf
          (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))) =
        (GlobalPlace.rationalInfinity k).order f +
          differentialOrder (k := k) (F := RatFunc k)
            (GlobalPlace.rationalInfinity k)
            (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
            (functionFieldDifferentialGenerator_ne_zero
              (k := k) (F := RatFunc k)) :=
      differentialOrder_smul (k := k) (F := RatFunc k)
        (GlobalPlace.rationalInfinity k) f hf
        (functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
        (functionFieldDifferentialGenerator_ne_zero (k := k) (F := RatFunc k))
    _ = (GlobalPlace.rationalInfinity k).order f - 2 := by
      rw [differentialOrder_generator_rationalInfinity]
      ring
end QEC.Coding.AlgebraicGeometry.Differential
