-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsGLPermSL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:06:19.416785+00:00
-- url     : https://prove2.me/submissions/fde64b96-970a-4be6-9bab-05c43fb45800

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeEffectiveCovers
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckePeterssonIntegrals
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSHeckeCommonDomain

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open Complex MeasureTheory Set UpperHalfPlane Filter Topology
open scoped MatrixGroups UpperHalfPlane ModularForm Modular NNReal ENNReal Pointwise
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (γ : SL(2,ℤ)) :
    (MulAction.toPerm (Matrix.SpecialLinearGroup.mapGL ℝ γ) : Equiv.Perm ℍ)=
      (MulAction.toPerm γ : Equiv.Perm ℍ) := by
  apply Equiv.ext
  intro τ
  change Matrix.SpecialLinearGroup.mapGL ℝ γ • τ = γ • τ
  exact (ModularGroup.sl_moeb γ τ).symm
end QEC.Coding.TannerLiftedProduct
