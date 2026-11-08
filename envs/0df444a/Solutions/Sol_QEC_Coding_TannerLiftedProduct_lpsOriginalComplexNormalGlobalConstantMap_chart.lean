-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGlobalConstantMap_chart
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T06:59:15.424412+00:00
-- url     : https://prove2.me/submissions/7951a819-1d84-43ac-9d6c-82118f194a23

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (b : Bool) :
    lpsOriginalComplexNormalGlobalConstantMap N hpos ≫
      (lpsOriginalComplexNormalGluedChartMap N hpos b).appTop =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
      (lpsOriginalComplexChartToSpecC N hpos b).appTop := by
  unfold lpsOriginalComplexNormalGlobalConstantMap
  rw [Category.assoc, ← Scheme.Hom.comp_appTop,
    lpsOriginalComplexNormalGluedToSpecC_chart]
end QEC.Coding.TannerLiftedProduct
