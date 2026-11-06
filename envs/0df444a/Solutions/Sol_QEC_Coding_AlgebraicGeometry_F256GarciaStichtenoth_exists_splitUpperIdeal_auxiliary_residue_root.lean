-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_splitUpperIdeal_auxiliary_residue_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:51:53.267375+00:00
-- url     : https://prove2.me/submissions/2d7aad48-06f9-4c38-89ba-c0febb5c3b39

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ResidualPolynomial
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SplitIntegralClosure
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_splitIntegralAuxiliaryCoordinate
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_splitIntegralAuxiliaryCoordinate_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_algebraMap_reciprocalUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralRoot
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_coe_stepIntegralUniformizer
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_eq_algebraMap_of_stepAuxiliaryPolynomial_aeval_eq_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_stepAuxiliaryPolynomial_natDegree
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.algebraMap_reciprocalUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralRoot
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_stepIntegralUniformizer
attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.stepAuxiliaryPolynomial_natDegree
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


attribute [local simp] QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.coe_splitIntegralAuxiliaryCoordinate
section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem aeval_stepAuxiliaryPolynomial
    {E : Type*} [Field E] [Algebra F256 E] (a : F256) (y : E) :
    Polynomial.aeval y (stepAuxiliaryPolynomial a) =
      y ^ 16 + (y - algebraMap F256 E (a ^ 17)) := by
  rw [stepAuxiliaryPolynomial, map_add, map_pow, aeval_X, map_sub, aeval_C]
  rw [Polynomial.aeval_X]
private theorem quotient_base_eq_constant
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (R : Ideal (SplitIntegralClosure Q P x hx)) [R.IsMaximal]
    [R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing)]
    (y : Q.place.valuationRing) :
    Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx) y) =
      Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place (Q.evaluate y))) := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  have hresidue : Q.place.residue y =
      Q.place.constantsToResidue (Q.evaluate y) := by
    calc
      Q.place.residue y =
          Q.constantsEquiv (Q.constantsEquiv.symm (Q.place.residue y)) := by
        rw [Q.constantsEquiv.apply_symm_apply]
      _ = Q.place.constantsToResidue (Q.evaluate y) := by
        rw [Q.constantsEquiv_apply]
        rfl
  have hbase : y - GlobalPlace.constantsToValuationRing Q.place (Q.evaluate y) ∈
      IsLocalRing.maximalIdeal Q.place.valuationRing := by
    rw [← GlobalPlace.residue_eq_zero_iff, map_sub]
    change Q.place.residue y - Q.place.constantsToResidue (Q.evaluate y) = 0
    rw [hresidue, sub_self]
  rw [← map_sub]
  change y - GlobalPlace.constantsToValuationRing Q.place (Q.evaluate y) ∈
    Ideal.under Q.place.valuationRing R
  rw [← (inferInstance : R.LiesOver
    (IsLocalRing.maximalIdeal Q.place.valuationRing)).over]
  exact hbase
end
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
end

set_option autoImplicit false
open Polynomial
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (R : Ideal (SplitIntegralClosure Q P x hx)) [R.IsMaximal]
    [R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing)] :
    ∃ b ∈ f256ArtinSchreierRoots (Q.evaluateRegular x hregular),
      splitIntegralAuxiliaryCoordinate Q P x hx hregular -
          algebraMap Q.place.valuationRing (SplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place b) ∈ R := by
  let O := Q.place.valuationRing
  let S := SplitIntegralClosure Q P x hx
  let E := S ⧸ R
  let xO : O := splitBaseCoordinate Q x hregular
  let zS : S := splitIntegralAuxiliaryCoordinate Q P x hx hregular
  letI : Field E := Ideal.Quotient.field R
  let constantsToE : F256 →+* E :=
    (Ideal.Quotient.mk R).comp
      ((algebraMap O S).comp (GlobalPlace.constantsToValuationRing Q.place))
  letI : Algebra F256 E := constantsToE.toAlgebra
  have hbase := quotient_base_eq_constant Q P x hx R xO
  have hbase' :
      Ideal.Quotient.mk R (algebraMap O S xO) =
        algebraMap F256 E (Q.evaluate xO) := by
    change Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SplitIntegralClosure Q P x hx) xO) =
      Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place (Q.evaluate xO)))
    exact hbase
  have hbase17 :
      Ideal.Quotient.mk R (algebraMap O S (xO ^ 17)) =
        algebraMap F256 E ((Q.evaluate xO) ^ 17) := by
    change Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SplitIntegralClosure Q P x hx) (xO ^ 17)) =
      algebraMap F256 E ((Q.evaluate xO) ^ 17)
    rw [map_pow, map_pow, hbase', map_pow]
  have hequation := congrArg (Ideal.Quotient.mk R)
    (splitIntegralAuxiliaryCoordinate_equation Q P x hx hregular)
  have hroot : Polynomial.aeval (Ideal.Quotient.mk R zS)
      (stepAuxiliaryPolynomial (Q.evaluate xO)) = 0 := by
    rw [aeval_stepAuxiliaryPolynomial]
    change (Ideal.Quotient.mk R zS) ^ 16 +
      ((Ideal.Quotient.mk R zS) -
        algebraMap F256 E ((Q.evaluate xO) ^ 17)) = 0
    change Ideal.Quotient.mk R
        (zS ^ 16 + zS) =
      Ideal.Quotient.mk R (algebraMap O S (xO ^ 17)) at hequation
    have hequation' :
        (Ideal.Quotient.mk R zS) ^ 16 + Ideal.Quotient.mk R zS =
          algebraMap F256 E ((Q.evaluate xO) ^ 17) := by
      calc
        (Ideal.Quotient.mk R zS) ^ 16 + Ideal.Quotient.mk R zS =
            Ideal.Quotient.mk R (zS ^ 16) + Ideal.Quotient.mk R zS := by
          rw [← (Ideal.Quotient.mk R).map_pow]
        _ = Ideal.Quotient.mk R (zS ^ 16 + zS) :=
          ((Ideal.Quotient.mk R).map_add _ _).symm
        _ = Ideal.Quotient.mk R (algebraMap O S (xO ^ 17)) := hequation
        _ = algebraMap F256 E ((Q.evaluate xO) ^ 17) := hbase17
    linear_combination hequation'
  obtain ⟨b, hb, hz⟩ :=
    exists_eq_algebraMap_of_stepAuxiliaryPolynomial_aeval_eq_zero
      (Q.evaluate xO) (Ideal.Quotient.mk R zS) hroot
  refine ⟨b, ?_, ?_⟩
  · simpa only [xO, splitBaseCoordinate, RationalPlace.evaluateRegular] using hb
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    change Ideal.Quotient.mk R zS - algebraMap F256 E b = 0
    rw [hz, sub_self]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
