-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChart_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:19:11.014024+00:00
-- url     : https://prove2.me/submissions/fd4ced97-ad2d-46ce-8c41-1effa207332d

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCharacteristicZeroSmooth
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dedekindFiniteType_smoothCharZero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalInfinityChart_finiteType


set_option autoImplicit false
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    letI : Algebra ℂ (lpsOriginalComplexNormalInfinityChart N hpos) :=
      (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
    Algebra.Smooth ℂ (lpsOriginalComplexNormalInfinityChart N hpos) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let R := lpsOriginalComplexNormalInfinityChart N hpos
  let : Algebra ℂ R := (lpsOriginalComplexInfinityConstantRingHom N hpos).toAlgebra
  let : IsDedekindDomain R := lpsOriginalInfinityChart_isDedekindDomain N hpos
  let : Algebra.FiniteType ℂ R := lpsOriginalInfinityChart_finiteType N hpos
  exact QEC.Coding.AlgebraicGeometry.dedekindFiniteType_smoothCharZero ℂ R
end QEC.Coding.TannerLiftedProduct
