-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalComplexNormalGlobalConstantMap_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T07:09:09.749193+00:00
-- url     : https://prove2.me/submissions/8074822d-f3d9-4ba3-b833-7acabbed9cee

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Differentials_AffineDifferentials
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalComplexNormalCharts
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalDifferentialSheaf
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalComplexNormalGlobalConstantMap_chart

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N)
local notation "X" => lpsOriginalComplexNormalGluedScheme N hpos
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    lpsOriginalComplexNormalGlobalConstantMap N hpos ≫
      (lpsOriginalComplexNormalGluedChartMap N hpos false).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of (lpsOriginalComplexNormalZeroChart N hpos))).hom =
    CommRingCat.ofHom (lpsOriginalComplexZeroConstantRingHom N hpos) := by
  have h := congrArg
    (fun t : CommRingCat.of ℂ ⟶
        Γ(Spec (CommRingCat.of (lpsOriginalComplexNormalZeroChart N hpos)), ⊤) =>
      t ≫ (Scheme.ΓSpecIso
        (CommRingCat.of (lpsOriginalComplexNormalZeroChart N hpos))).hom)
    (lpsOriginalComplexNormalGlobalConstantMap_chart N hpos false)
  trans ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
    (lpsOriginalComplexChartToSpecC N hpos false).appTop) ≫
      (Scheme.ΓSpecIso
        (CommRingCat.of (lpsOriginalComplexNormalZeroChart N hpos))).hom
  · exact (Category.assoc _ _ _).symm.trans h
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫
    (Spec.map (CommRingCat.ofHom (lpsOriginalComplexZeroConstantRingHom N hpos))).appTop ≫
    (Scheme.ΓSpecIso (CommRingCat.of (lpsOriginalComplexNormalZeroChart N hpos))).hom = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
end QEC.Coding.TannerLiftedProduct
