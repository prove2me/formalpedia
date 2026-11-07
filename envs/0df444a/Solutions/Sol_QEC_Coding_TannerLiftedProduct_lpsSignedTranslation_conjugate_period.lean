-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsSignedTranslation_conjugate_period
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T23:36:58.430374+00:00
-- url     : https://prove2.me/submissions/7364570d-1c01-4ecd-aa7c-71481f381cba

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelCuspArithmetic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalFilledAnalytic
import Mathlib.Topology.Maps.Proper.Basic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalLevelMapGeometry
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsSignedTranslation_commute_period

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex Filter Topology Set
open scoped MatrixGroups UpperHalfPlane ModularForm Manifold ContDiff Modular Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (g : GL (Fin 2) ℝ) (x t : ℝ)
    (hg : g = Matrix.GeneralLinearGroup.upperRightHom x ∨
      g = -Matrix.GeneralLinearGroup.upperRightHom x) :
    g * Matrix.GeneralLinearGroup.upperRightHom t * g⁻¹ =
      Matrix.GeneralLinearGroup.upperRightHom t := by
  rw [lpsSignedTranslation_commute_period g x t hg, mul_assoc, mul_inv_cancel, mul_one]
end QEC.Coding.TannerLiftedProduct
