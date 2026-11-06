-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_simplePoleRatio_square_add_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:31:12.694667+00:00
-- url     : https://prove2.me/submissions/76c78acc-3506-4d6c-9607-6f651f078fdb

import Mathlib.FieldTheory.Perfect
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_QuadraticRefinement
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_TwoChartGlobalPlace
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreierCancellation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_unit_square_add_maximalIdeal
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_quadraticArtinSchreierUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_quadraticArtinSchreierIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_inv
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_order_mul
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_regularAt_iff_order_nonnegative
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
private theorem valuation_eq_one_of_order_eq_zero
    (P : GlobalPlace F256 K) {z : K} (hz : z ≠ 0)
    (horder : P.order z = 0) : P.valuation z = 1 := by
  have hvaluation_ne : P.valuation z ≠ 0 :=
    P.valuation.ne_zero_iff.mpr hz
  have hlog : WithZero.log (P.valuation z) = 0 := by
    unfold GlobalPlace.order at horder
    omega
  calc
    P.valuation z = WithZero.exp (WithZero.log (P.valuation z)) :=
      (WithZero.exp_log hvaluation_ne).symm
    _ = 1 := by rw [hlog]; simp
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
variable [Algebra (Polynomial F256) K] [Algebra (RatFunc F256) K]
variable [IsScalarTower (Polynomial F256) (RatFunc F256) K]
variable [_root_.FunctionField F256 K]
variable [Algebra.IsSeparable (RatFunc F256) K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (P : GlobalPlace F256 K) (z₁ z₂ : K)
    (hz₁ : P.order z₁ = -1) (hz₂ : P.order z₂ = -1) :
    ∃ u w : P.valuationRing,
      z₂ / z₁ = (u : K) ^ 2 + (w : K) ∧
        u ∉ IsLocalRing.maximalIdeal P.valuationRing ∧
        w ∈ IsLocalRing.maximalIdeal P.valuationRing := by
  have hz₁_ne : z₁ ≠ 0 := ne_zero_of_order_eq_neg_one P hz₁
  have hz₂_ne : z₂ ≠ 0 := ne_zero_of_order_eq_neg_one P hz₂
  have hratio_ne : z₂ / z₁ ≠ 0 := div_ne_zero hz₂_ne hz₁_ne
  have hratio_order : P.order (z₂ / z₁) = 0 := by
    rw [div_eq_mul_inv, P.order_mul hz₂_ne (inv_ne_zero hz₁_ne),
      P.order_inv, hz₁, hz₂]
    norm_num
  have hratio_regular : GlobalPlace.RegularAt P (z₂ / z₁) :=
    (P.regularAt_iff_order_nonnegative hratio_ne).mpr (by omega)
  let q : P.valuationRing :=
    ⟨z₂ / z₁, (P.mem_valuationRing_iff (z₂ / z₁)).mpr hratio_regular⟩
  have hq_not_maximal : q ∉ IsLocalRing.maximalIdeal P.valuationRing := by
    rw [Valuation.mem_maximalIdeal_iff]
    change ¬P.valuation (z₂ / z₁) < 1
    rw [valuation_eq_one_of_order_eq_zero P hratio_ne hratio_order]
    exact lt_irrefl 1
  letI : Finite P.residueField := GlobalPlace.finite_residueField P
  obtain ⟨u, w, hq, hu, hw⟩ :=
    exists_unit_square_add_maximalIdeal P q hq_not_maximal
  refine ⟨u, w, ?_, hu, hw⟩
  have hq_field := congrArg (fun y : P.valuationRing => (y : K)) hq
  simp only [q, map_add, map_pow] at hq_field ⊢
  exact hq_field
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
