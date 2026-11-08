-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGlobalConstantMap_infinity_affine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:12:57.472622+00:00
-- url     : https://prove2.me/submissions/e3adaabb-20df-4028-959d-6240fd618a78

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGlobalConstantMap_infinity

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
local notation "Z" => lpsOriginalComplexNormalZeroChart N hpos
local notation "I" => lpsOriginalComplexNormalInfinityChart N hpos
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChartDifferentialAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChartDifferentialAlgebra
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChartDifferentialSMul
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChartDifferentialModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChartDifferentialSMulComm
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChartOmegaSMul
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalZeroChartOmegaModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChartDifferentialSMul
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChartDifferentialModule
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChartDifferentialSMulComm
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChartOmegaSMul
attribute [local instance] QEC.Coding.TannerLiftedProduct.lpsOriginalInfinityChartOmegaModule
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    lpsOriginalComplexNormalGlobalConstantMap N hpos ≫
      (lpsOriginalComplexNormalGluedChartMap N hpos true).appTop =
    affineDifferentialGlobalConstantMap ℂ (CommRingCat.of I) := by
  apply (cancel_mono (Scheme.ΓSpecIso (CommRingCat.of I)).hom).mp
  change _ = (CommRingCat.ofHom (lpsOriginalComplexInfinityConstantRingHom N hpos) ≫
    (Scheme.ΓSpecIso (CommRingCat.of I)).inv) ≫ (Scheme.ΓSpecIso (CommRingCat.of I)).hom
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact lpsOriginalComplexNormalGlobalConstantMap_infinity N hpos
end QEC.Coding.TannerLiftedProduct
