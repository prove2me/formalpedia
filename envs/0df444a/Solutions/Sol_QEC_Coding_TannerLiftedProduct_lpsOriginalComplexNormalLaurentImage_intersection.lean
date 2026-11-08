-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalLaurentImage_intersection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:03:58.22893+00:00
-- url     : https://prove2.me/submissions/2c6ac513-a3e5-4f10-8944-8f15b0e2e8b1

import Definitions.Def_QEC_Coding_AlgebraicGeometry_SchemeOverlapImages
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialImages
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_schemeGlueOverlap_image_intersection
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
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) (hpos : 0 < N)
attribute [local instance] QEC.Coding.TannerLiftedProduct.originalOverlapImageOpenImmersion
attribute [local instance] QEC.Coding.TannerLiftedProduct.originalChartImageOpenImmersion
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    (lpsOriginalComplexNormalSchemeOverlapMap N hpos false ≫
      lpsOriginalComplexNormalGluedChartMap N hpos false).opensRange =
      lpsOriginalComplexNormalChartImage N hpos false ⊓
        lpsOriginalComplexNormalChartImage N hpos true := by
  let D := lpsOriginalComplexNormalSchemeGlueData N hpos
  have e : D.V (false, true) =
      Spec (.of (lpsOriginalComplexNormalLaurentChart N hpos)) := by
    simp [D, lpsOriginalComplexNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData', lpsOriginalComplexNormalSchemeGlueDataPrime]
  have hf : D.f false true = eqToHom e ≫
      lpsOriginalComplexNormalSchemeOverlapMap N hpos false := by
    simp [D, lpsOriginalComplexNormalSchemeGlueData,
      CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f',
      lpsOriginalComplexNormalSchemeGlueDataPrime]
  have h := schemeGlueOverlap_image_intersection D false true
  have he : D.f false true ≫ D.ι false = eqToHom e ≫
      (lpsOriginalComplexNormalSchemeOverlapMap N hpos false ≫
        lpsOriginalComplexNormalGluedChartMap N hpos false) := by
    have hcomp := congrArg (fun a : D.V (false, true) ⟶
      lpsOriginalComplexNormalSchemeChart N hpos false =>
        a ≫ lpsOriginalComplexNormalGluedChartMap N hpos false) hf
    exact hcomp.trans (Category.assoc (eqToHom e)
      (lpsOriginalComplexNormalSchemeOverlapMap N hpos false)
      (lpsOriginalComplexNormalGluedChartMap N hpos false))
  have hi : IsOpenImmersion (D.f false true) := D.f_open false true
  have hj : IsOpenImmersion (D.ι false) := Scheme.GlueData.ι_isOpenImmersion D false
  let hc : IsOpenImmersion (D.f false true ≫ D.ι false) :=
    @IsOpenImmersion.comp _ _ _ (D.f false true) (D.ι false) hi hj
  have hr : (D.f false true ≫ D.ι false).opensRange =
      (lpsOriginalComplexNormalSchemeOverlapMap N hpos false ≫
        lpsOriginalComplexNormalGluedChartMap N hpos false).opensRange := by
    apply TopologicalSpace.Opens.ext
    change Set.range (D.f false true ≫ D.ι false) = Set.range
      (lpsOriginalComplexNormalSchemeOverlapMap N hpos false ≫
        lpsOriginalComplexNormalGluedChartMap N hpos false)
    rw [he]
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨(eqToHom e) z, (Scheme.Hom.comp_apply _ _ z).symm⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, hz⟩ := (eqToHom e).homeomorph.surjective y
      refine ⟨z, ?_⟩
      exact (Scheme.Hom.comp_apply _ _ z).trans
        (congrArg (lpsOriginalComplexNormalSchemeOverlapMap N hpos false ≫
          lpsOriginalComplexNormalGluedChartMap N hpos false) hz)
  exact hr.symm.trans h
end QEC.Coding.TannerLiftedProduct
