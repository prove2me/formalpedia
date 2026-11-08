-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChart_smooth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:21:20.043825+00:00
-- url     : https://prove2.me/submissions/fb1c2845-6aa1-4160-bad1-f1f417d9bbd1

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Schemes_CharZeroCurveSmoothness
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalIntegerFlatModel
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLocalKaehlerInjective
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalNormalizationComparison
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalCharacteristicZeroSmooth
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_dedekindFiniteType_smoothCharZero
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalZeroChart_finiteType


set_option autoImplicit false
open scoped TensorProduct
open CategoryTheory AlgebraicGeometry
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (N : ℕ) [NeZero N] (hpos : 0 < N) :
    letI := lpsOriginalJFractionEmbedding.toAlgebra
    letI : Algebra ℂ (lpsOriginalComplexNormalZeroChart N hpos) :=
      (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
    Algebra.Smooth ℂ (lpsOriginalComplexNormalZeroChart N hpos) := by
  let := lpsOriginalJFractionEmbedding.toAlgebra
  let R := lpsOriginalComplexNormalZeroChart N hpos
  let : Algebra ℂ R := (lpsOriginalComplexZeroConstantRingHom N hpos).toAlgebra
  let : IsDedekindDomain R := lpsOriginalZeroChart_isDedekindDomain N hpos
  let : Algebra.FiniteType ℂ R := lpsOriginalZeroChart_finiteType N hpos
  exact QEC.Coding.AlgebraicGeometry.dedekindFiniteType_smoothCharZero ℂ R
end QEC.Coding.TannerLiftedProduct
