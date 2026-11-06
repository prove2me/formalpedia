-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth.sourceSplitUpperRationalPlace_evaluate_sourceStepEmbedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:40:06.980864+00:00
-- url     : https://prove2.me/submissions/a49f553d-5581-4511-a6cf-9760f045328e

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceRationalSplitting
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_SourceSplitEvaluation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_AffinePlace_residue_eq_zero_iff
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
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_residue_eq_zero_iff
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_constants
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RationalPlace_evaluate_eq_zero_iff
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



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
noncomputable section
variable {K : Type*} [Field K] [Algebra F256 K]
namespace QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
theorem _root_.solution
    (Q : RationalPlace F256 K) (P : GlobalPlace F256 K) (x : K)
    (hx : P.order x = -1)
    (hregular : GlobalPlace.RegularAt Q.place x)
    (hsplit : galoisBaseWValue (Q.evaluateRegular x hregular) ≠ 0)
    (c : LinearMap.ker f256ArtinSchreier)
    (f : K) (hf : GlobalPlace.RegularAt Q.place f) :
    (sourceSplitUpperRationalPlace Q P x hx hregular hsplit c).evaluateRegular
        (sourceStepEmbedding P x hx f)
        (sourceSplitAbovePlace_sourceStepEmbedding_regular
          Q P x hx c f hf) =
      Q.evaluateRegular f hf := by
  let O := Q.place.valuationRing
  let S := SourceSplitIntegralClosure Q P x hx
  let L := SourceStepField P x hx
  let H := sourceSplitUpperHeightOne Q P x hx c
  let U := sourceSplitUpperRationalPlace Q P x hx hregular hsplit c
  let m : Ideal O := IsLocalRing.maximalIdeal O
  letI : H.asIdeal.LiesOver m := by
    change ((sourceSplitUpperPrime Q P x hx c).1).LiesOver m
    infer_instance
  let fO : O :=
    ⟨f, (GlobalPlace.mem_valuationRing_iff Q.place f).mpr hf⟩
  let a : F256 := Q.evaluateRegular f hf
  let fU : U.place.valuationRing :=
    ⟨sourceStepEmbedding P x hx f,
      (GlobalPlace.mem_valuationRing_iff U.place _).mpr
        (sourceSplitAbovePlace_sourceStepEmbedding_regular
          Q P x hx c f hf)⟩
  let aU : U.place.valuationRing :=
    GlobalPlace.constantsToValuationRing U.place a
  have hbase : fO - GlobalPlace.constantsToValuationRing Q.place a ∈
      IsLocalRing.maximalIdeal O := by
    rw [← Q.evaluate_eq_zero_iff, map_sub, Q.evaluate_constants]
    change a - a = 0
    exact sub_self a
  have hupper : algebraMap O S
      (fO - GlobalPlace.constantsToValuationRing Q.place a) ∈ H.asIdeal := by
    rw [← Ideal.mem_under]
    rw [← (inferInstance : H.asIdeal.LiesOver m).over]
    exact hbase
  have hlt : H.valuation L
      (algebraMap S L
        (algebraMap O S
          (fO - GlobalPlace.constantsToValuationRing Q.place a))) < 1 :=
    (H.valuation_lt_one_iff_mem (K := L) _).2 hupper
  change U.constantsEquiv.symm (U.place.residue fU) = a
  apply U.constantsEquiv.injective
  rw [U.constantsEquiv.apply_symm_apply, U.constantsEquiv_apply]
  change U.place.residue fU = U.place.residue aU
  rw [← sub_eq_zero, ← map_sub, GlobalPlace.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  change H.valuation L
    (sourceStepEmbedding P x hx f - algebraMap F256 L a) < 1
  simp only [map_sub, IsScalarTower.algebraMap_apply] at hlt ⊢
  exact hlt
end QEC.Coding.AlgebraicGeometry.F256GarciaStichtenoth
