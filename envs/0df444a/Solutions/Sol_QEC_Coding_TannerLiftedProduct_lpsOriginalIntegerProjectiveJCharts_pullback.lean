-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerProjectiveJCharts_pullback
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:56:59.749781+00:00
-- url     : https://prove2.me/submissions/2776164d-1b7d-4606-8938-aa3413fdc1fc

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerModelCharts
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_jacobiFourSquareSeries_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_even
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_eval_zero_odd
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_one
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsHeckePolynomial_zero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsQuadraticE2TwistModularForm_apply
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_jacobiFourSquareSeries_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_even
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_eval_zero_odd
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_one
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsHeckePolynomial_zero
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsQuadraticE2TwistModularForm_apply
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open scoped UpperHalfPlane MatrixGroups
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    IsPullback (lpsOriginalIntegerProjectiveJOverlapMap false)
      (lpsOriginalIntegerProjectiveJOverlapMap true)
      (lpsOriginalIntegerProjectiveJChartMap false)
      (lpsOriginalIntegerProjectiveJChartMap true) := by
  let D := lpsOriginalIntegerProjectiveJGlueData
  have e : D.V (false,true)=Spec (.of (LaurentPolynomial ℤ)) := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerProjectiveJGlueDataPrime]
  have e' : D.V (true,false)=Spec (.of (LaurentPolynomial ℤ)) := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerProjectiveJGlueDataPrime]
  have hf : D.f false true = eqToHom e ≫
      lpsOriginalIntegerProjectiveJOverlapMap false := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerProjectiveJGlueDataPrime]
  have hf' : D.f true false = eqToHom e' ≫
      lpsOriginalIntegerProjectiveJOverlapMap true := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerProjectiveJGlueDataPrime]
  have ht : D.t false true = eqToHom e ≫ eqToHom e'.symm := by
    simp [D,lpsOriginalIntegerProjectiveJGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerProjectiveJGlueDataPrime]
  have h : IsPullback (D.f false true) (D.t false true ≫ D.f true false)
      (D.ι false) (D.ι true) :=
    { w := (D.glue_condition false true).symm
      isLimit' := ⟨D.vPullbackConeIsLimit false true⟩ }
  apply h.of_iso (eqToIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, eqToIso.hom, Category.comp_id] using hf
  · simp only [Iso.refl_hom, eqToIso.hom, Category.comp_id]
    rw [ht,hf']
    simp only [Category.assoc,eqToHom_trans_assoc,eqToHom_refl,Category.id_comp]
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    rfl
  · simp only [Iso.refl_hom,Category.comp_id,Category.id_comp]
    rfl
end QEC.Coding.TannerLiftedProduct
