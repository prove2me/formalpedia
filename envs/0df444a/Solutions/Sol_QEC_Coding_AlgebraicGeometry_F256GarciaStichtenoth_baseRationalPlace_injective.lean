-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.baseRationalPlace_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:27:48.717289+00:00
-- url     : https://prove2.me/submissions/0f966252-2dcb-418d-9c9a-2402d8b10a8b

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
theorem _root_.solution :
    Function.Injective (fun a : BasePoint => (baseRationalPlace a).place) := by
  intro a b hab
  change GlobalPlace.rationalAdic (baseHeightOne a) =
    GlobalPlace.rationalAdic (baseHeightOne b) at hab
  have hoption : (some (baseHeightOne a) :
      Option (IsDedekindDomain.HeightOneSpectrum F256[X])) =
      some (baseHeightOne b) := by
    exact (GlobalPlace.rationalPlaceEquiv (k := F256)).injective (by
      simpa only [GlobalPlace.rationalPlaceEquiv_apply_some] using hab)
  have hheight : baseHeightOne a = baseHeightOne b := Option.some.inj hoption
  have hpoly : (X - C (a : F256) : F256[X]) = X - C (b : F256) := by
    calc
      X - C (a : F256) =
          GlobalPlace.rationalAdicPolynomial (baseHeightOne a) :=
        (baseRationalAdicPolynomial a).symm
      _ = GlobalPlace.rationalAdicPolynomial (baseHeightOne b) := by rw [hheight]
      _ = X - C (b : F256) := baseRationalAdicPolynomial b
  apply Units.ext
  have hcoeff := congrArg (fun p : F256[X] => p.coeff 0) hpoly
  simpa using hcoeff
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
