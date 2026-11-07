-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.f256PuncturedMultiplicationCode_distance_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:47:50.595195+00:00
-- url     : https://prove2.me/submissions/a6d25e9c-4689-4177-829e-4045481535b8

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureEvaluation
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_NormalClosureShortening
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_degree_upper
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_f256MultiplicationDivisor_selected_eq_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_distance_lower_bound


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
attribute [local instance 2500] Algebra.toSMul Algebra.toModule
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    (((f256GarciaStichtenothLength i + 3) / 4 - f256MultiplicationLogicalCount i : ℕ) : WithTop ℕ) ≤
      HypergraphProduct.extendedMinimumDistance (f256PuncturedMultiplicationCode i) := by
  classical
  have h := agEvaluation_distance_lower_bound (f256MultiplicationDivisor i)
    (fun j : F256MultiplicationRetained i => f256GarciaStichtenothSelectedRationalPlace i j.val)
    ((f256GarciaStichtenothSelectedPlace_injective i).comp Subtype.val_injective)
    (fun j => f256MultiplicationDivisor_selected_eq_zero i j.val)
  rw [f256MultiplicationRetained_card] at h
  have hu := f256MultiplicationDivisor_degree_upper i
  have hK := f256MultiplicationLogicalCount_lt_fifth i
  have hb : (f256GarciaStichtenothLength i + 3) / 4 - f256MultiplicationLogicalCount i ≤
      Int.toNat ((f256GarciaStichtenothLength i - f256MultiplicationLogicalCount i : ℕ) -
        Divisor.degree GlobalPlace.residueDegree (f256MultiplicationDivisor i)) := by
    omega
  exact le_trans (WithTop.coe_le_coe.mpr hb) h
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
