-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexChartToSpecC_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:25:58.533707+00:00
-- url     : https://prove2.me/submissions/f711fa0f-5a04-4e1a-bf8f-ff1e3d9df43b

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCharacteristicZeroSmooth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroChart_smooth
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityChart_smooth

set_option autoImplicit false
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (N : ℕ) [NeZero N] (hpos : 0 < N) (b : Bool) :
    Smooth (lpsOriginalComplexChartToSpecC N hpos b) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  cases b with
  | false =>
    let : Algebra ℂ (lpsOriginalComplexNormalZeroChart N hpos) :=
      (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
    let : Algebra.Smooth ℂ (lpsOriginalComplexNormalZeroChart N hpos) :=
      lpsOriginalZeroChart_smooth N hpos
    change Smooth (Spec.map (CommRingCat.ofHom
      (lpsOriginalComplexZeroConstantRingHom N hpos)))
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    change (algebraMap ℂ _).Smooth
    rw [RingHom.smooth_algebraMap]
    infer_instance
  | true =>
    let : Algebra ℂ (lpsOriginalComplexNormalInfinityChart N hpos) :=
      (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
    let : Algebra.Smooth ℂ (lpsOriginalComplexNormalInfinityChart N hpos) :=
      lpsOriginalInfinityChart_smooth N hpos
    change Smooth (Spec.map (CommRingCat.ofHom
      (lpsOriginalComplexInfinityConstantRingHom N hpos)))
    apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    change (algebraMap ℂ _).Smooth
    rw [RingHom.smooth_algebraMap]
    infer_instance
end QEC.Coding.TannerLiftedProduct
