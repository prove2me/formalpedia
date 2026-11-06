-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.exists_sourceSplitUpperIdeal_coordinate_residue_root
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:25:53.473939+00:00
-- url     : https://prove2.me/submissions/fb19f312-f949-40ea-96da-c2c42fe8323e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitAlgebra
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitIntegralClosure
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceStepRhs_evaluateRegular
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_sourceSplitIntegralCoordinate_equation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_F256GarciaStichtenoth_exists_eq_algebraMap_of_sourceStepResidualPolynomial_aeval_eq_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residue_eq_zero_iff

section
open Polynomial
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
private theorem aeval_sourceStepResidualPolynomial
    {E : Type*} [Field E] [Algebra F256 E]
    (a : GaloisBaseSplitPoint) (y : E) :
    Polynomial.aeval y (sourceStepResidualPolynomial a) =
      y ^ 16 + (y - algebraMap F256 E (sourceStepRhs (a : F256))) := by
  rw [sourceStepResidualPolynomial, map_add, map_pow,
    Polynomial.aeval_X, map_sub, Polynomial.aeval_C]
  rw [Polynomial.aeval_X]
private theorem sourceSplitQuotient_base_eq_constant
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (R : Ideal (SourceSplitIntegralClosure Q P x hx)) [R.IsMaximal]
    [R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing)]
    (y : Q.place.valuationRing) :
    Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SourceSplitIntegralClosure Q P x hx) y) =
      Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SourceSplitIntegralClosure Q P x hx)
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
  have hbase :
      y - GlobalPlace.constantsToValuationRing Q.place (Q.evaluate y) ∈
        IsLocalRing.maximalIdeal Q.place.valuationRing := by
    rw [← GlobalPlace.residue_eq_zero_iff, map_sub]
    change Q.place.residue y -
        Q.place.constantsToResidue (Q.evaluate y) = 0
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
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (R : Ideal (SourceSplitIntegralClosure Q P x hx)) [R.IsMaximal]
    [R.LiesOver (IsLocalRing.maximalIdeal Q.place.valuationRing)] :
    ∃ b ∈ sourceStepArtinSchreierRoots
        (⟨Q.evaluateRegular x hregular, hsplit⟩ : GaloisBaseSplitPoint),
      sourceSplitIntegralCoordinate Q P x hx hregular hsplit -
          algebraMap Q.place.valuationRing
            (SourceSplitIntegralClosure Q P x hx)
            (GlobalPlace.constantsToValuationRing Q.place b) ∈ R := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let E := S ⧸ R
  let a : GaloisBaseSplitPoint :=
    ⟨Q.evaluateRegular x hregular, hsplit⟩
  let yS := sourceSplitIntegralCoordinate Q P x hx hregular hsplit
  let rO := sourceSplitBaseRhs Q x hregular hsplit
  letI : Field E := Ideal.Quotient.field R
  let constantsToE : F256 →+* E :=
    (Ideal.Quotient.mk R).comp
      ((algebraMap O S).comp (GlobalPlace.constantsToValuationRing Q.place))
  letI : Algebra F256 E := constantsToE.toAlgebra
  have hbase := sourceSplitQuotient_base_eq_constant Q P x hx R rO
  have hbase' :
      Ideal.Quotient.mk R (algebraMap O S rO) =
        algebraMap F256 E (sourceStepRhs (a : F256)) := by
    change Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SourceSplitIntegralClosure Q P x hx) rO) =
      Ideal.Quotient.mk R
        (algebraMap Q.place.valuationRing
          (SourceSplitIntegralClosure Q P x hx)
          (GlobalPlace.constantsToValuationRing Q.place
            (sourceStepRhs (a : F256))))
    rw [← sourceStepRhs_evaluateRegular Q x hregular hsplit]
    exact hbase
  have hequation := congrArg (Ideal.Quotient.mk R)
    (sourceSplitIntegralCoordinate_equation
      Q P x hx hregular hsplit)
  have hroot : Polynomial.aeval (Ideal.Quotient.mk R yS)
      (sourceStepResidualPolynomial a) = 0 := by
    rw [aeval_sourceStepResidualPolynomial]
    change (Ideal.Quotient.mk R yS) ^ 16 +
      ((Ideal.Quotient.mk R yS) -
        algebraMap F256 E (sourceStepRhs (a : F256))) = 0
    change Ideal.Quotient.mk R (yS ^ 16 + yS) =
      Ideal.Quotient.mk R (algebraMap O S rO) at hequation
    have hequation' :
        (Ideal.Quotient.mk R yS) ^ 16 + Ideal.Quotient.mk R yS =
          algebraMap F256 E (sourceStepRhs (a : F256)) := by
      calc
        (Ideal.Quotient.mk R yS) ^ 16 + Ideal.Quotient.mk R yS =
            Ideal.Quotient.mk R (yS ^ 16) + Ideal.Quotient.mk R yS := by
          rw [← (Ideal.Quotient.mk R).map_pow]
        _ = Ideal.Quotient.mk R (yS ^ 16 + yS) :=
          ((Ideal.Quotient.mk R).map_add _ _).symm
        _ = Ideal.Quotient.mk R (algebraMap O S rO) := hequation
        _ = algebraMap F256 E (sourceStepRhs (a : F256)) := hbase'
    linear_combination hequation'
  obtain ⟨b, hb, hy⟩ :=
    exists_eq_algebraMap_of_sourceStepResidualPolynomial_aeval_eq_zero
      a (Ideal.Quotient.mk R yS) hroot
  refine ⟨b, ?_, ?_⟩
  · exact hb
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    change Ideal.Quotient.mk R yS - algebraMap F256 E b = 0
    rw [hy, sub_self]
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
