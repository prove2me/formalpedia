-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalChartImage_cover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:09:46.510122+00:00
-- url     : https://prove2.me/submissions/5db74a28-0f46-4fd3-acdc-6ec9beb97391

import Definitions.Def_QEC_Coding_AlgebraicGeometry_SchemeOverlapImages
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialImages
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGluedChartMap_cover


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
    lpsOriginalComplexNormalChartImage N hpos false ⊔
      lpsOriginalComplexNormalChartImage N hpos true = ⊤ := by
  apply le_antisymm le_top
  intro x _
  obtain ⟨b, y, hy⟩ := lpsOriginalComplexNormalGluedChartMap_cover N hpos x
  cases b
  · exact Or.inl ⟨y, hy⟩
  · exact Or.inr ⟨y, hy⟩
end QEC.Coding.TannerLiftedProduct
