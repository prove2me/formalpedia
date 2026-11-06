-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.rationalAdic_order_ge_neg_one_of_isGlobalSimplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:48:18.533234+00:00
-- url     : https://prove2.me/submissions/0e6ddb7d-d1e9-4c72-9dd9-4ea643e09f45

import Mathlib.Algebra.Squarefree.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimplePoleDenominator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_smul_generator_rationalAdic
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_FunctionFieldDifferential_functionFieldDifferentialGenerator_ne_zero


set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open QEC.Coding.AlgebraicGeometry.Differential
open FunctionFieldDifferential
variable {k : Type*} [Field k] [Finite k]
namespace QEC.Coding.AlgebraicGeometry.Differential
theorem _root_.solution
    (f : RatFunc k) (hf : f ≠ 0)
    (homega : IsGlobalSimplePole
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k)))
    (p : IsDedekindDomain.HeightOneSpectrum k[X]) :
    -1 ≤ (GlobalPlace.rationalAdic p).order f := by
  have hsimple := homega (GlobalPlace.rationalAdic p)
  have horder :=
    (mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
      (k := k) (F := RatFunc k) (GlobalPlace.rationalAdic p)
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
      (smul_ne_zero hf
        (functionFieldDifferentialGenerator_ne_zero
          (k := k) (F := RatFunc k)))).mp hsimple
  rw [differentialOrder_smul_generator_rationalAdic
    (k := k) p f hf] at horder
  exact horder
end QEC.Coding.AlgebraicGeometry.Differential
