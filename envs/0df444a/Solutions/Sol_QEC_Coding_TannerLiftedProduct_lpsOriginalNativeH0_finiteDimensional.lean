-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsOriginalNativeH0_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T13:39:47.662652+00:00
-- url     : https://prove2.me/submissions/6314ab79-c8f2-4b0e-96da-e617cd0743ba

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalRegularDifferentialFiniteness
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSOriginalGlobalDifferentialFiniteness
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsOriginalRegularKaehler_finiteDimensional


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
    FiniteDimensional ℂ Γ(lpsOriginalComplexNormalDifferentialSheaf N hpos, ⊤) := by
  let : FiniteDimensional ℂ (lpsOriginalNativeRegularKaehlerSubmodule N hpos) :=
    lpsOriginalRegularKaehler_finiteDimensional N hpos
  let e := lpsOriginalNativeH0RegularCovectorLinearEquiv N hpos hN
  exact FiniteDimensional.of_injective e.toLinearMap e.injective
end QEC.Coding.TannerLiftedProduct
