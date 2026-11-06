-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.zeroBaseRationalPlace_evaluate_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:34:21.56256+00:00
-- url     : https://prove2.me/submissions/dc84c347-8604-460e-8a37-7331d0148c53

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicPolynomialLogarithmicResidue
import Mathlib.RingTheory.Polynomial.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ZeroPlace
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Differential_coe_rationalAdicPolynomialDifferential
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
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
attribute [local simp] QEC.Coding.AlgebraicGeometry.Differential.coe_rationalAdicPolynomialDifferential
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
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



set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution :
    zeroBaseRationalPlace.evaluateRegular RatFunc.X
        zeroBaseRationalPlace_X_regular = 0 := by
  have hxmem : RatFunc.X ∈
      (GlobalPlace.rationalAdic zeroBaseHeightOne).valuationRing := by
    simpa only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
      RatFunc.algebraMap_X] using
        (GlobalPlace.rationalAdicPolynomialToValuationRing
          zeroBaseHeightOne Polynomial.X).property
  change zeroBaseResidueEquiv.symm
      ((GlobalPlace.rationalAdic zeroBaseHeightOne).residue
        ⟨RatFunc.X, hxmem⟩) = 0
  apply zeroBaseResidueEquiv.injective
  rw [zeroBaseResidueEquiv.apply_symm_apply, map_zero]
  let xO := GlobalPlace.rationalAdicPolynomialToValuationRing
    zeroBaseHeightOne Polynomial.X
  have hinput :
      (⟨RatFunc.X, hxmem⟩ :
        (GlobalPlace.rationalAdic zeroBaseHeightOne).valuationRing) = xO := by
    apply Subtype.ext
    simp only [xO, GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
      RatFunc.algebraMap_X]
  rw [hinput]
  have hmk :
      AdjoinRoot.mk (GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne)
          Polynomial.X = 0 := by
    rw [AdjoinRoot.mk_eq_zero, zeroBaseRationalAdicPolynomial]
  calc
    (GlobalPlace.rationalAdic zeroBaseHeightOne).residue xO =
        GlobalPlace.rationalAdicResidueEquiv zeroBaseHeightOne
          (AdjoinRoot.mk
            (GlobalPlace.rationalAdicPolynomial zeroBaseHeightOne)
            Polynomial.X) := by
          exact (GlobalPlace.rationalAdicResidueEquiv_mk
            zeroBaseHeightOne Polynomial.X).symm
    _ = 0 := by rw [hmk, map_zero]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
