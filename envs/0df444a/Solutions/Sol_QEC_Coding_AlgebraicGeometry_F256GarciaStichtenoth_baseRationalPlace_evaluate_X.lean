-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.baseRationalPlace_evaluate_X
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:28:39.337198+00:00
-- url     : https://prove2.me/submissions/e70d5b6f-5d60-43f6-b1a9-ba9c8b44aadc

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_FixedFieldArtinSchreier
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Rational_AdicResidue
import Mathlib.RingTheory.Polynomial.Quotient
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation



set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (a : BasePoint) :
    (baseRationalPlace a).evaluateRegular RatFunc.X
        (baseRationalPlace_X_regular a) = (a : F256) := by
  have hxmem : RatFunc.X ∈
      (GlobalPlace.rationalAdic (baseHeightOne a)).valuationRing := by
    simpa only [GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
      RatFunc.algebraMap_X] using
        (GlobalPlace.rationalAdicPolynomialToValuationRing
          (baseHeightOne a) Polynomial.X).property
  change (baseResidueEquiv a).symm
      ((GlobalPlace.rationalAdic (baseHeightOne a)).residue
        ⟨RatFunc.X, hxmem⟩) = (a : F256)
  apply (baseResidueEquiv a).injective
  rw [(baseResidueEquiv a).apply_symm_apply]
  rw [baseResidueEquiv_apply]
  let xO := GlobalPlace.rationalAdicPolynomialToValuationRing
    (baseHeightOne a) Polynomial.X
  have hinput :
      (⟨RatFunc.X, hxmem⟩ :
        (GlobalPlace.rationalAdic (baseHeightOne a)).valuationRing) = xO := by
    apply Subtype.ext
    simp only [xO, GlobalPlace.coe_rationalAdicPolynomialToValuationRing,
      RatFunc.algebraMap_X]
  rw [hinput]
  have hmk :
      AdjoinRoot.mk (GlobalPlace.rationalAdicPolynomial (baseHeightOne a))
          Polynomial.X =
        algebraMap F256
          (AdjoinRoot (GlobalPlace.rationalAdicPolynomial (baseHeightOne a)))
          (a : F256) := by
    rw [baseRationalAdicPolynomial, AdjoinRoot.mk_X,
      AdjoinRoot.algebraMap_eq]
    rw [← sub_eq_zero, ← AdjoinRoot.eval₂_root
      (Polynomial.X - Polynomial.C (a : F256))]
    simp
  calc
    (GlobalPlace.rationalAdic (baseHeightOne a)).residue xO =
        GlobalPlace.rationalAdicResidueEquiv (baseHeightOne a)
          (AdjoinRoot.mk
            (GlobalPlace.rationalAdicPolynomial (baseHeightOne a))
            Polynomial.X) := by
          exact (GlobalPlace.rationalAdicResidueEquiv_mk
            (baseHeightOne a) Polynomial.X).symm
    _ = GlobalPlace.rationalAdicResidueEquiv (baseHeightOne a)
          (algebraMap F256
            (AdjoinRoot (GlobalPlace.rationalAdicPolynomial (baseHeightOne a)))
            (a : F256)) := by rw [hmk]
    _ = GlobalPlace.constantsToResidue
          (GlobalPlace.rationalAdic (baseHeightOne a)) (a : F256) :=
      rationalAdicResidueEquiv_algebraMap (baseHeightOne a) (a : F256)
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
