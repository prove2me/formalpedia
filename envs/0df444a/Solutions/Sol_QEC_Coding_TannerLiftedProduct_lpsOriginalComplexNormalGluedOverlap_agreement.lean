-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGluedOverlap_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:55:43.324505+00:00
-- url     : https://prove2.me/submissions/479b44e1-a589-4b05-8bc8-5819f3dc3bd4

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLaurentNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerProperModel
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_NormalizationBaseChange
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.OpenImmersion
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
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
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open scoped TensorProduct
noncomputable section
local notation "JC" => FractionRing (Polynomial ℂ)
attribute [local instance] QEC.Coding.TannerLiftedProduct.complexGluingDictionary001
set_option backward.isDefEq.respectTransparency false
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) (hN : 0<N) :
    lpsOriginalComplexNormalSchemeOverlapMap N hN false ≫
      lpsOriginalComplexNormalGluedChartMap N hN false=
    lpsOriginalComplexNormalSchemeOverlapMap N hN true ≫
      lpsOriginalComplexNormalGluedChartMap N hN true := by
  let D := lpsOriginalComplexNormalSchemeGlueData N hN
  change lpsOriginalComplexNormalSchemeOverlapMap N hN false ≫ D.ι false =
    lpsOriginalComplexNormalSchemeOverlapMap N hN true ≫ D.ι true
  have e : D.V (false,true)=Spec (.of (lpsOriginalComplexNormalLaurentChart N hN)) := by
    simp [D,lpsOriginalComplexNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalComplexNormalSchemeGlueDataPrime]
  have e' : D.V (true,false)=Spec (.of (lpsOriginalComplexNormalLaurentChart N hN)) := by
    simp [D,lpsOriginalComplexNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalComplexNormalSchemeGlueDataPrime]
  have hf : D.f false true = eqToHom e ≫
      lpsOriginalComplexNormalSchemeOverlapMap N hN false := by
    simp [D,lpsOriginalComplexNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalComplexNormalSchemeGlueDataPrime]
  have hf' : D.f true false = eqToHom e' ≫
      lpsOriginalComplexNormalSchemeOverlapMap N hN true := by
    simp [D,lpsOriginalComplexNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalComplexNormalSchemeGlueDataPrime]
  have ht : D.t false true = eqToHom e ≫ eqToHom e'.symm := by
    simp [D,lpsOriginalComplexNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalComplexNormalSchemeGlueDataPrime]
  have h := D.glue_condition false true
  rw [hf,hf',ht] at h
  have hh := congrArg (fun f : D.V (false,true) ⟶ D.glued => eqToHom e.symm ≫ f) h.symm
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using hh
end QEC.Coding.TannerLiftedProduct
