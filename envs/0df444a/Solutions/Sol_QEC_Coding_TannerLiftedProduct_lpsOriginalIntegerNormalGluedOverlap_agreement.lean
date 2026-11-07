-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalIntegerNormalGluedOverlap_agreement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T02:56:12.628033+00:00
-- url     : https://prove2.me/submissions/39666167-6214-4862-9dbf-11f4db315d26

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
theorem _root_.solution
    (N : ℕ) (hN : 0<N) :
    lpsOriginalIntegerNormalSchemeOverlapMap N hN false ≫
      lpsOriginalIntegerNormalGluedChartMap N hN false=
    lpsOriginalIntegerNormalSchemeOverlapMap N hN true ≫
      lpsOriginalIntegerNormalGluedChartMap N hN true := by
  let D := lpsOriginalIntegerNormalSchemeGlueData N hN
  change lpsOriginalIntegerNormalSchemeOverlapMap N hN false ≫ D.ι false =
    lpsOriginalIntegerNormalSchemeOverlapMap N hN true ≫ D.ι true
  have e : D.V (false,true)=Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have e' : D.V (true,false)=Spec (.of (lpsOriginalIntegerNormalLaurentChart N hN)) := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have hf : D.f false true = eqToHom e ≫
      lpsOriginalIntegerNormalSchemeOverlapMap N hN false := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have hf' : D.f true false = eqToHom e' ≫
      lpsOriginalIntegerNormalSchemeOverlapMap N hN true := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',CategoryTheory.GlueData'.f',
      lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have ht : D.t false true = eqToHom e ≫ eqToHom e'.symm := by
    simp [D,lpsOriginalIntegerNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData',lpsOriginalIntegerNormalSchemeGlueDataPrime]
  have h := D.glue_condition false true
  rw [hf,hf',ht] at h
  have hh := congrArg (fun f : D.V (false,true) ⟶ D.glued => eqToHom e.symm ≫ f) h.symm
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using hh
end QEC.Coding.TannerLiftedProduct
