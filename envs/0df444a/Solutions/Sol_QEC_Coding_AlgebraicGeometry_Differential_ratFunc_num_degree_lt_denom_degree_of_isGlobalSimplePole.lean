-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.Differential.ratFunc_num_degree_lt_denom_degree_of_isGlobalSimplePole
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:51:04.137395+00:00
-- url     : https://prove2.me/submissions/a2cdfe6f-f845-4c0f-8ae1-079ae4022677

import Mathlib.Algebra.Squarefree.Basic
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_RatFuncDifferentialOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_SimplePoleDenominator
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_rationalInfinity_order_ge_one_of_isGlobalSimplePole
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalBaseInfinityCancellation_rationalInfinity_order_eq_denomDegree_sub_numDegree


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
    f.num.degree < f.denom.degree := by
  have hinfinity : 1 ≤ (GlobalPlace.rationalInfinity k).order f :=
    rationalInfinity_order_ge_one_of_isGlobalSimplePole f hf homega
  rw [RationalBaseInfinityCancellation.rationalInfinity_order_eq_denomDegree_sub_numDegree
    k f hf] at hinfinity
  have hnat : f.num.natDegree < f.denom.natDegree := by
    omega
  rw [Polynomial.degree_eq_natDegree (RatFunc.num_ne_zero hf),
    Polynomial.degree_eq_natDegree (RatFunc.denom_ne_zero f)]
  exact WithBot.coe_lt_coe.mpr hnat
end QEC.Coding.AlgebraicGeometry.Differential
