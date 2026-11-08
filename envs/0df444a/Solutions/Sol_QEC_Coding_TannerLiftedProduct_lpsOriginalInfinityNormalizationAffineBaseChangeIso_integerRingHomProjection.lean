-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityNormalizationAffineBaseChangeIso_integerRingHomProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:59:25.202363+00:00
-- url     : https://prove2.me/submissions/66e33da8-329f-432e-ad2e-a21df9739164

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_ChartBaseChange
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalNormalizationBaseChange
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_NormalizationBaseChange_normalizationTensorSpecIso_baseRingHomProjection


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open QEC.Coding.AlgebraicGeometry.NormalizationBaseChange
open scoped TensorProduct
noncomputable section
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary001
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary002
variable (N : ℕ) [NeZero N] (hN : 0 < N)
local notation "JQ" => FractionRing (Polynomial ℚ)
local notation "JC" => FractionRing (Polynomial ℂ)
local notation "FQ" => lpsOriginalGeneratedFunctionFieldQ N hN
local notation "FC" => lpsOriginalGeneratedFunctionField N hN
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary003
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary004
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary005
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary006
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary007
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary008
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary009
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary010
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary011
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary012
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary013
local notation "ICL" => integralClosure (LaurentPolynomial ℂ) FC
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary014
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary015
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeDictionary016
local notation "IC0" => integralClosure (Polynomial ℂ) FC
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroComplexAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroIntegerAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroIntegerModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroSelfAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroSelfSMul
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroSelfModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeZeroIntegerSelfTower
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeLaurentSelfAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeLaurentSelfSMul
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeLaurentSelfModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeLaurentIntegerSelfTower
attribute [local irreducible] lpsOriginalIntegerLaurentChartComplexNormalizationAlgEquiv
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeInfinityPolynomialAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeInfinityComplexPolynomialTower
local notation "ICInfinity" => integralClosure (Polynomial ℂ) FC
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeInfinityComplexAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeInfinityIntegerAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeInfinityIntegerModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeInfinitySelfAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeInfinitySelfSMul
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeInfinitySelfModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.affineBaseChangeInfinityIntegerSelfTower
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    (lpsOriginalInfinityNormalizationAffineBaseChangeIso N hN).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (lpsOriginalComplexInfinityIntegerChartRingHom N hN)) := by
  exact normalizationTensorSpecIso_baseRingHomProjection
    (lpsOriginalIntegerInfinityChartComplexNormalizationAlgEquiv N hN)
end QEC.Coding.TannerLiftedProduct
