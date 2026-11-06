-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceGaloisBaseParameter_sub_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:48:38.216203+00:00
-- url     : https://prove2.me/submissions/f84c6a31-09cb-4df3-a927-9a1eab01d616

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitOrder
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSelectedPlaceOrder
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_sourceStepUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceSplitIntegralCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_sourceStepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepResidualPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_sourceStepUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceSplitIntegralCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_sourceStepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceStepResidualPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
private theorem sourceSelectedSplitPolynomial_derivative :
    sourceSelectedSplitPolynomial.derivative =
      (Polynomial.X ^ 16 + Polynomial.X) ^ 14 := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  rw [sourceSelectedSplitPolynomial, Polynomial.derivative_sub,
    Polynomial.derivative_pow, Polynomial.derivative_add,
    Polynomial.derivative_X_pow, Polynomial.derivative_X,
    Polynomial.derivative_one]
  reduce_mod_char!
  simp
private theorem sourceSelectedSplitPolynomial_ne_zero :
    sourceSelectedSplitPolynomial ≠ 0 := by
  intro hzero
  have hderivative := congrArg Polynomial.derivative hzero
  rw [sourceSelectedSplitPolynomial_derivative, map_zero] at hderivative
  exact (pow_ne_zero 14
    (Polynomial.monic_X_pow_add (by norm_num)).ne_zero) hderivative
private theorem sourceGaloisBaseParameter_sub_one_eq_polynomial (m : ℕ) :
    sourceGaloisBaseParameter m - 1 =
      algebraMap (RatFunc F256) (SourceField m)
        (algebraMap (Polynomial F256) (RatFunc F256)
          sourceSelectedSplitPolynomial) := by
  rw [sourceGaloisBaseParameter]
  calc
    algebraMap (RatFunc F256) (SourceField m) galoisBaseZ - 1 =
        algebraMap (RatFunc F256) (SourceField m) (galoisBaseZ - 1) := by
      rw [map_sub, map_one]
    _ = algebraMap (RatFunc F256) (SourceField m)
        (algebraMap (Polynomial F256) (RatFunc F256)
          sourceSelectedSplitPolynomial) := by
      congr 1
      simp [sourceSelectedSplitPolynomial, galoisBaseZ, galoisBaseW,
        RatFunc.algebraMap_X]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (m : ℕ) :
    sourceGaloisBaseParameter m - 1 ≠ 0 := by
  rw [sourceGaloisBaseParameter_sub_one_eq_polynomial]
  simpa only [map_zero] using
    (algebraMap (RatFunc F256) (SourceField m)).injective.ne
      (RatFunc.algebraMap_ne_zero sourceSelectedSplitPolynomial_ne_zero)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
