-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalCuspForms_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T14:35:52.173593+00:00
-- url     : https://prove2.me/submissions/5eb0b92f-81fa-459f-8343-e2b8a026611f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRegularDifferentialFiniteness
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalDifferentialFiniteness
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalNativeH0_finiteDimensional

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
open QEC.Coding.AlgebraicGeometry
open QEC.Coding.TannerLiftedProduct
open CategoryTheory _root_.AlgebraicGeometry Opposite QEC.Coding.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry MatrixGroups UpperHalfPlane ModularForm Modular Manifold ContDiff
noncomputable section
variable (N : ℕ) [NeZero N] (hpos : 0 < N) (hN : 4 ∣ N)
attribute [local instance] originalNativeGlobalComplexModule
include hpos hN
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution :
    FiniteDimensional ℂ
      (CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) := by
  let : FiniteDimensional ℂ Γ(lpsOriginalComplexNormalDifferentialSheaf N hpos, ⊤) :=
    lpsOriginalNativeH0_finiteDimensional N hpos hN
  let e := lpsOriginalNativeH0CuspFormLinearEquiv N hpos hN
  exact FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
end QEC.Coding.TannerLiftedProduct
