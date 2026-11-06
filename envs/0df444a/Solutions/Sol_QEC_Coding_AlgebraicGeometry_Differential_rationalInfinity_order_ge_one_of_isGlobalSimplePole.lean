-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.rationalInfinity_order_ge_one_of_isGlobalSimplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:49:28.843969+00:00
-- url     : https://prove2.me/submissions/579420f7-b353-4b61-9388-280eb3c4eb20

import Mathlib.Algebra.Squarefree.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimplePoleDenominator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_differentialOrder_smul_generator_rationalInfinity
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
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))) :
    1 ≤ (GlobalPlace.rationalInfinity k).order f := by
  have hsimple := homega (GlobalPlace.rationalInfinity k)
  have horder :=
    (mem_simplePoleDifferentialLattice_iff_differentialOrder_neg_one
      (k := k) (F := RatFunc k) (GlobalPlace.rationalInfinity k)
      (f • functionFieldDifferentialGenerator (k := k) (F := RatFunc k))
      (smul_ne_zero hf
        (functionFieldDifferentialGenerator_ne_zero
          (k := k) (F := RatFunc k)))).mp hsimple
  rw [differentialOrder_smul_generator_rationalInfinity
    (k := k) f hf] at horder
  omega
end QEC.Coding.AlgebraicGeometry.Differential
