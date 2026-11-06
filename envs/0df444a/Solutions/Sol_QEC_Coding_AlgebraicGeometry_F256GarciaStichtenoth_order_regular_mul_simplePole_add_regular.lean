-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.order_regular_mul_simplePole_add_regular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:05:44.729126+00:00
-- url     : https://prove2.me/submissions/758902c0-2343-4e0a-a091-99bb1b09cb1b

import Mathlib.FieldTheory.Perfect
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreierCancellation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_quadraticArtinSchreierUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_quadraticArtinSchreierIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
open scoped Polynomial RatFunc WithZero
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem ne_zero_of_order_eq_neg_one
    (P : GlobalPlace F256 K) {z : K} (hz : P.order z = -1) : z ≠ 0 := by
  intro hzero
  subst z
  simp [GlobalPlace.order] at hz
variable [Algebra (Polynomial F256) K] [Algebra (RatFunc F256) K]
variable [IsScalarTower (Polynomial F256) (RatFunc F256) K]
variable [_root_.FunctionField F256 K]
variable [Algebra.IsSeparable (RatFunc F256) K]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open scoped Polynomial RatFunc WithZero
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (x c r : K)
    (hx : P.order x = -1)
    (hc : GlobalPlace.RegularAt P c)
    (hr : GlobalPlace.RegularAt P r) :
    P.order (c * x + r) = -1 ∨ 0 ≤ P.order (c * x + r) := by
  have hx_ne : x ≠ 0 := ne_zero_of_order_eq_neg_one P hx
  have hxvaluation_ne : P.valuation x ≠ 0 :=
    P.valuation.ne_zero_iff.mpr hx_ne
  have hxlog : WithZero.log (P.valuation x) = 1 := by
    unfold GlobalPlace.order at hx
    omega
  have hxvaluation : P.valuation x = WithZero.exp (1 : ℤ) := by
    calc
      P.valuation x = WithZero.exp (WithZero.log (P.valuation x)) :=
        (WithZero.exp_log hxvaluation_ne).symm
      _ = WithZero.exp (1 : ℤ) := by rw [hxlog]
  have hcxvaluation : P.valuation (c * x) ≤ WithZero.exp (1 : ℤ) := by
    rw [P.valuation.map_mul, hxvaluation]
    simpa only [one_mul] using
      mul_le_mul_left hc (WithZero.exp (1 : ℤ))
  have hone_le_exp : (1 : ℤᵐ⁰) ≤ WithZero.exp (1 : ℤ) := by
    simpa only [WithZero.exp_zero] using
      (WithZero.exp_le_exp.mpr (show (0 : ℤ) ≤ 1 by omega))
  have hrvaluation : P.valuation r ≤ WithZero.exp (1 : ℤ) :=
    hr.trans hone_le_exp
  have hsumvaluation :
      P.valuation (c * x + r) ≤ WithZero.exp (1 : ℤ) :=
    (P.valuation.map_add (c * x) r).trans
      (max_le hcxvaluation hrvaluation)
  by_cases hsum : c * x + r = 0
  · right
    rw [hsum]
    simp [GlobalPlace.order]
  · have hsumvaluation_ne : P.valuation (c * x + r) ≠ 0 :=
      P.valuation.ne_zero_iff.mpr hsum
    have hlog_le : WithZero.log (P.valuation (c * x + r)) ≤ 1 :=
      (WithZero.log_le_iff_le_exp hsumvaluation_ne (a := 1)).mpr
        hsumvaluation
    have horder_ge : -1 ≤ P.order (c * x + r) := by
      unfold GlobalPlace.order
      omega
    omega
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
