-- Prove2me | solution 1 for QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticAdicCyclicBasis_equivFun_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T18:24:44.251953+00:00
-- url     : https://prove2.me/submissions/0d8df9fb-99a8-4f04-a4ff-0b7c2fd58ac0

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadSpecialization
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Arithmetic_PrasadDenominatorCorrection

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped TensorProduct
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger.arithmeticFinitePlaceDecidableEq
namespace QEC.Coding.HighDimensionalExpander.CartwrightSteger
theorem _root_.solution
    (P : BasePrime) (r : Rank)
    (v : IsDedekindDomain.HeightOneSpectrum (ArithmeticRing P))
    (x : CyclicAlgebra P r)
    (p : Fin r.matrixRank × Fin r.matrixRank) :
    (arithmeticAdicCyclicBasis P r v).equivFun
        (TensorProduct.tmul (FunctionField P) 1 x) p =
      algebraMap (FunctionField P)
        (v.adicCompletion (FunctionField P))
          ((functionFieldCyclicBasis P r).equivFun x p) := by
  rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply,
    arithmeticAdicCyclicBasis, Module.Basis.baseChange_repr_tmul]
  rw [Algebra.smul_def, mul_one]
end QEC.Coding.HighDimensionalExpander.CartwrightSteger
