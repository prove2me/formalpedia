-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.galoisBaseZValue_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:54:48.36894+00:00
-- url     : https://prove2.me/submissions/28e97195-d9d2-498b-8c71-2f751e50ee39

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_BasePlaces
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_GaloisBase
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_rationalAdicPolynomialToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalAdicResidueEquiv_mk
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_none
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_rationalPlaceEquiv_apply_some
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_f256_card
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_rationalAdicPolynomialToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalAdicResidueEquiv_mk
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_none
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.rationalPlaceEquiv_apply_some
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation


section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
private theorem galoisBaseWValue_pow_sixteen (a : F256) :
    galoisBaseWValue a ^ 16 = galoisBaseWValue a := by
  letI : CharP F256 2 :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod 2) F256).injective 2
  have ha : a ^ 256 = a := by
    simpa only [f256_card] using FiniteField.pow_card a
  rw [galoisBaseWValue_eq]
  calc
    (a ^ 16 + a) ^ 16 = (a ^ 16) ^ 16 + a ^ 16 := by
      have hport := (add_pow_char_pow (a ^ 16) a 2 4)
      norm_num only [show (2 : ℕ) ^ 4 = 16 by norm_num] at hport
      change (a ^ 16 + a) ^ 16 = (a ^ 16) ^ 16 + a ^ 16
      exact hport
    _ = a ^ 256 + a ^ 16 := by rw [← pow_mul]
    _ = a + a ^ 16 := by rw [ha]
    _ = a ^ 16 + a := add_comm _ _
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution (a : F256) :
    galoisBaseZValue a = 1 ↔ galoisBaseWValue a ≠ 0 := by
  constructor
  · intro hz hw
    rw [galoisBaseZValue, hw] at hz
    simpa using hz
  · intro hw
    apply mul_left_cancel₀ hw
    calc
      galoisBaseWValue a * galoisBaseWValue a ^ 15 =
          galoisBaseWValue a ^ 16 := by ring
      _ = galoisBaseWValue a := galoisBaseWValue_pow_sixteen a
      _ = galoisBaseWValue a * 1 := (mul_one _).symm
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
