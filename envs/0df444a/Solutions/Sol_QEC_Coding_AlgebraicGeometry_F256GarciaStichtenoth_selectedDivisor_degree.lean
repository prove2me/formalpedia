-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.selectedDivisor_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:33:52.504614+00:00
-- url     : https://prove2.me/submissions/e9cbcd8f-7085-4a33-a26b-9eea2045cb90

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Enumeration
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Divisors
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_selectedPlace_residueDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitUpperRationalPlace_place
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.splitUpperRationalPlace_place
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
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
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
noncomputable section
private theorem divisor_degree_single (i : ℕ) (degreeOf :
    GlobalPlace F256 (Field (i + 2)) → ℕ)
    (P : GlobalPlace F256 (Field (i + 2))) (coefficient : ℤ) :
    Divisor.degree degreeOf (Finsupp.single P coefficient) =
      coefficient * (degreeOf P : ℤ) := by
  simp [Divisor.degree, Divisor.degreeHom]
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
open scoped BigOperators
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (i : ℕ) :
    Divisor.degree GlobalPlace.residueDegree (selectedDivisor i) =
      selectedLength i := by
  classical
  unfold selectedDivisor
  change
    Divisor.degreeHom GlobalPlace.residueDegree
        (∑ j : Fin (selectedLength i),
          Finsupp.single (selectedPlace i j) (1 : ℤ)) =
      selectedLength i
  rw [map_sum]
  calc
    (∑ j : Fin (selectedLength i),
        Divisor.degreeHom GlobalPlace.residueDegree
          (Finsupp.single (selectedPlace i j) (1 : ℤ))) =
        ∑ _j : Fin (selectedLength i), (1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro j _
      change
        Divisor.degree GlobalPlace.residueDegree
            (Finsupp.single (selectedPlace i j) (1 : ℤ)) = 1
      rw [divisor_degree_single, selectedPlace_residueDegree]
      simp
    _ = selectedLength i := by simp
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
